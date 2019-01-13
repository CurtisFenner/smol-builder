return [===[
package core;

class Out {
	foreign static println!(message String) Unit;
}

class ASCII {
	foreign static formatInt(value Int) String;
}

interface Showable {
	static showType() String;
	method show() String;
}

union Option[#T | #T is Eq] {
	var some #T;
	var none Unit;

	static makeSome(value #T) Option[#T]
	ensures return is some
	ensures return.some == value {
		return new(some = value);
	}

	static makeNone() Option[#T]
	ensures return is none {
		return new(none = unit);
	}

	method get() #T
	requires this is some
	ensures return == this.some {
		var out #T = this.some;
		assert out == this.some;
		return out;
	}
}

class Pair[#A, #B | #A is Eq, #B is Eq] is Eq {
	var left #A;
	var right #B;

	method getLeft() #A
	ensures return == this.left {
		return this.left;
	}

	method getRight() #B
	ensures return == this.right {
		return this.right;
	}

	static make(left #A, right #B) Pair[#A, #B]
	ensures return.getLeft() == left
	ensures return.getRight() == right {
		return new(left = left, right = right);
	}

	method eq(other Pair[#A, #B]) Boolean {
		return (this.left == other.left).and(this.right == other.right);
	}
}

interface Orderable {
	// RETURNS true when this is smaller than other in this ordering.
	method lessThan(other #Self) Boolean
	// ensures this.lessThan(this).not()
	// ensures forall (middle #Self) return when this.lessThan(middle).and( middle.lessThan(other)  )
	;
}

interface Eq {
	// RETURNS true when these elements are equal such that
	// (a == b) => f(a) == f(b)
	method eq(other #Self) Boolean;
}

class WInt is Eq {
	var value Int;

	method get() Int ensures return == this.value {
		return this.value;
	}

	static make(n Int) WInt ensures return.get() == n {
		var out WInt = new(value = n);
		assert out.value == n;
		assert out.get() == n;
		return out;
	}

	method eq(other WInt) Boolean {
		return this.value == other.value;
	}
}

]===]
