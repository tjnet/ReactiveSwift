import Result

// The bidirectional partial binding operator. It is used in conjunction with `<~` which
// completes partial bindings.
infix operator ~>: BindingPrecedence

/// Represents an entity that can form a bidirectional value binding with another entity.
/// The binding monitors mutations of `self` through the modifier signal provided by
/// `self`, while it accepts mutations from the binding through its binding target.
///
/// To establish a bidirectional binding, use the `~>` operator to construct a partial
/// binding with a binding policy and an endpoint. Then use `<~` to complete the partial
/// binding with another endpoint.
///
/// ```
/// let 🌈 = MutableProperty<String>("🌈")
/// let 🦄 = MutableProperty<String>("🦄")
///
/// let partialBinding = .preferLeft ~> 🌈
/// let disposable = 🦄 <~ partialBinding
///
/// // Inlined version
/// 🦄 <~ .preferLeft ~> 🌈
///
/// // The initial value is resolved using the `preferLeft`
/// // binding policy.
/// assert(🦄.value == "🦄")
/// assert(🌈.value == "🦄")
/// ```
///
/// # Consistency Gaurantees
public protocol BidirectionalBindingEndpointProvider {
	associatedtype Modifier: BidirectionalBindingEndpointModifier

	var bindingEndpoint: BidirectionalBindingEndpoint<Modifier> { get }
}

public protocol BidirectionalBindingEndpointModifier {
	associatedtype Value

	func modify(_ action: (inout Value) -> Void)
}

public struct BidirectionalBindingEndpoint<Modifier: BidirectionalBindingEndpointModifier> {
	fileprivate let scheduler: Scheduler?
	fileprivate let values: SignalProducer<Modifier, NoError>
	fileprivate let setter: ((inout Modifier.Value) -> Void) -> Void
	fileprivate let lifetime: Lifetime
}

public enum BidirectionalBindingPolicy {
	case preferLeft
	case preferRight
}

// Operator implementations.
extension BidirectionalBindingEndpointProvider {
	public static func ~> (policy: BidirectionalBindingPolicy, provider: Self) -> PartialBidirectionalBinding<Modifier> {
		return PartialBidirectionalBinding(provider.bindingEndpoint, policy: policy)
	}
}

public struct PartialBidirectionalBinding<Modifier: BidirectionalBindingEndpointModifier> {
	fileprivate let policy: BidirectionalBindingPolicy
	fileprivate let endpoint: BidirectionalBindingEndpoint<Modifier>

	fileprivate init(_ endpoint: BidirectionalBindingEndpoint<Modifier>, policy: BidirectionalBindingPolicy) {
		self.policy = policy
		self.endpoint = endpoint
	}

	@discardableResult
	public static func <~ <Provider: BidirectionalBindingEndpointProvider>(
		provider: Provider,
		partialBinding: PartialBidirectionalBinding<Modifier>
	) -> Disposable? where Modifier.Value == Provider.Modifier.Value {
		let arbitrator = BidirectionalBindingArbitrator(left: provider.bindingEndpoint, right: partialBinding.endpoint, policy: partialBinding.policy)
		return arbitrator.disposable
	}
}

private let noWriteback: Int32 = 0

#if os(iOS) || os(macOS) || os(tvOS) || os(watchOS)
private struct Counter {
	private var count: Int32 = 0

	static func ==(counter: inout Counter, value: Int32) -> Bool {
		return withUnsafeMutablePointer(to: &counter.count) { OSAtomicCompareAndSwap32Barrier(value, value, $0) }
	}

	static func +=(counter: inout Counter, value: Int32) {
		_ = withUnsafeMutablePointer(to: &counter.count) { OSAtomicAdd32Barrier(value, $0) }
	}

	static func -=(counter: inout Counter, value: Int32) {
		counter += -value
	}
}
#else
private typealias Counter = Atomic<Int32>

extension Atomic where Value == Int32 {
	convenience init() {
		self.init(0)
	}

	static func ==(counter: inout Counter, value: Int32) -> Bool {
		return modify { $0 == value }
	}

	static func +=(counter: inout Counter, value: Int32) {
		modify { $0 += counter }
	}

	static func -=(counter: inout Counter, value: Int32) {
		counter += -value
	}
}
#endif

private final class BidirectionalBindingArbitrator<LHSModifier, RHSModifier> where LHSModifier: BidirectionalBindingEndpointModifier, RHSModifier: BidirectionalBindingEndpointModifier, LHSModifier.Value == RHSModifier.Value {
	private typealias Value = LHSModifier.Value
	private typealias _Self = BidirectionalBindingArbitrator<LHSModifier, RHSModifier>

	private enum Endpoint {
		case none
		case left
		case right
	}

	private enum Container {
		case left(Value)
		case right(Value)
	}

	private let (endSignal, endObserver) = Signal<(), NoError>.pipe()
	private let policy: BidirectionalBindingPolicy
	let disposable: ActionDisposable

	private var isLHSWritingBack: Bool
	private var isRHSWritingBack: Bool
	private var outstandingLHSWriteback: Counter
	private var outstandingRHSWriteback: Counter

	private let lock: NSLock
	private var lastWritten: Endpoint
	private var writeForeign: (_Self, Container) -> Void

	private var isConflicting: Bool {
		return !(outstandingLHSWriteback == 0 && outstandingRHSWriteback == 0)
	}

	init(left: BidirectionalBindingEndpoint<LHSModifier>, right: BidirectionalBindingEndpoint<RHSModifier>, policy: BidirectionalBindingPolicy) {
		func setupLeft() {
			left.values.take(until: endSignal).startWithValues { modifier in
				guard !self.isLHSWritingBack else {
					self.isLHSWritingBack = false
					return
				}

				modifier.modify { value in
					if let writebackValue = self.resolve(.left(value)) {
						value = writebackValue
					}
				}
			}
		}

		func setupRight() {
			right.values.take(until: endSignal).startWithValues { modifier in
				guard !self.isRHSWritingBack else {
					self.isRHSWritingBack = false
					return
				}

				modifier.modify { value in
					if let writebackValue = self.resolve(.right(value)) {
						value = writebackValue
					}
				}
			}
		}

		self.lock = NSLock()
		self.isLHSWritingBack = false
		self.isRHSWritingBack = false
		self.outstandingLHSWriteback = Counter()
		self.outstandingRHSWriteback = Counter()
		self.lastWritten = .none

		self.policy = policy
		self.disposable = ActionDisposable(action: endObserver.sendCompleted)
		left.lifetime.observeEnded(endObserver.sendCompleted)
		right.lifetime.observeEnded(endObserver.sendCompleted)

		let leftScheduler = left.scheduler ?? ImmediateScheduler()
		let rightScheduler = right.scheduler ?? ImmediateScheduler()

		writeForeign = { [leftSetter = left.setter, rightSetter = right.setter] arbitrator, newValue in
			switch newValue {
			case let .left(newValue):
				arbitrator.lastWritten = .right
				arbitrator.outstandingLHSWriteback += 1

				leftScheduler.schedule {
					leftSetter { value in
						// The flag is cleared by the observer
						arbitrator.isLHSWritingBack = true
						value = newValue
					}
					arbitrator.outstandingLHSWriteback -= 1
				}

			case let .right(newValue):
				arbitrator.lastWritten = .left
				arbitrator.outstandingRHSWriteback += 1

				rightScheduler.schedule {
					rightSetter { value in
						arbitrator.isRHSWritingBack = true
						value = newValue
					}
					arbitrator.outstandingRHSWriteback -= 1
				}
			}
		}

		setupLeft()
		setupRight()
	}

	private func resolve(_ attemptedValue: Container) -> Value? {
		lock.lock()
		defer { lock.unlock() }

		// Abort writes only if the source endpoint is not preferred, and the last written
		// value is from the preferred endpoint.

		switch (isConflicting, attemptedValue, lastWritten, policy) {
		case (true, .left, .right, .preferRight):
			// LHS attempt. Last resolution is from RHS. Prefer RHS.
			fatalError("TODO: return last resolved value")

		case (true, .right, .left, .preferLeft):
			// RHS attempt. Last resolution is from LHS. Prefer LHS.
			fatalError("TODO: return last resolved value")

		case let (_, .left(value), _, _):
			writeForeign(self, .right(value))

		case let (_, .right(value), _, _):
			writeForeign(self, .left(value))
		}

		return nil
	}
}

// Bidirectional mapped properties.

public protocol BidirectionalTransform {
	associatedtype Value1
	associatedtype Value2

	func convert(_ value: Value1) -> Value2
	func convert(_ value: Value2) -> Value1
}

public struct AnyBidirectionalTransform<A, B>: BidirectionalTransform {
	public typealias Value1 = A
	public typealias Value2 = B

	private let convert1: (Value1) -> Value2
	private let convert2: (Value2) -> Value1

	public init<Transform: BidirectionalTransform>(reversing transform: Transform) where Transform.Value2 == Value1, Transform.Value1 == Value2 {
		self.init(transform.convert, transform.convert)
	}

	public init(_ forward: @escaping (Value1) -> Value2, _ reverse: @escaping (Value2) -> Value1) {
		self.convert1 = forward
		self.convert2 = reverse
	}

	public func convert(_ value: Value1) -> Value2 {
		return convert1(value)
	}

	public func convert(_ value: Value2) -> Value1 {
		return convert2(value)
	}
}

public final class TransformingProperty<Value>: MutablePropertyProtocol {
	private let cache: Property<Value>
	private let setter: (Value) -> Void

	public var value: Value {
		get { return cache.value }
		set { setter(newValue) }
	}

	public var producer: SignalProducer<Value, NoError> {
		return cache.producer
	}

	public var signal: Signal<Value, NoError> {
		return cache.signal
	}

	public let lifetime: Lifetime

	public init<P: MutablePropertyProtocol, Transform: BidirectionalTransform>(_ property: P, _ transform: Transform) where Transform.Value1 == P.Value, Transform.Value2 == Value {
		cache = property.map(transform.convert)
		setter = { property.value = transform.convert($0) }
		lifetime = property.lifetime
	}

	public convenience init<P: MutablePropertyProtocol, Transform: BidirectionalTransform>(_ property: P, _ transform: Transform) where Transform.Value2 == P.Value, Transform.Value1 == Value {
		self.init(property, AnyBidirectionalTransform(reversing: transform))
	}
}
