abstract sig Node {} {
	-- at most one parent
	lone this.~(left + right + middle)
}

sig TwoThreeNode extends Node {
	a: Int,
	b: lone Int,
	left: Node,
	right: Node,
	middle: lone Node
} {
	no left & right
	no left & middle
	no right & middle

	a != b

	-- 3-nodes have 2 values
	some middle iff some b

	-- Internal nodes (nodes with children) only have non-leaf children
	left in Leaf iff right in Leaf
	middle in TwoThreeNode => left in TwoThreeNode and right in TwoThreeNode -- can't use iff since middle can be none

	-- Left and right (and middle) are of the same height
	-- Enforce locally by stating that either both are internal or both are external	

	all d: left.*(@left + @right + @middle).(@a + @b) | a > d

	isTwoNode => {
		all d: right.*(@left + @right + @middle).(@a + @b) | a <= d

		left.isInternal iff right.isInternal
	}

	isThreeNode => {
		all d: middle.*(@left + @right + @middle).(@a + @b) | a <= d and b > d
		all d: right.*(@left + @right + @middle).(@a + @b) | b < d

		left.isInternal iff right.isInternal
		left.isInternal iff middle.isInternal
	}

}

sig Leaf extends Node {}

pred TwoThreeNode.isTwoNode {
	no this.middle
}

pred TwoThreeNode.isThreeNode {
	some this.middle
}

pred TwoThreeNode.isExternal {
	this.(left + right + middle) in Leaf
}

pred TwoThreeNode.isInternal {
	this.(left + right + middle) in TwoThreeNode
}

fun TwoThreeNode.leaves : set Leaf {
	this.^(left + right + middle) & Leaf
}

fun TwoThreeNode.height[l: Leaf] : Int {
	#{n: this.*(@left + @right + @middle) | l in n.^(@left + @right + @middle)}
}

fun TwoThreeNode.height : Int {
	max[1]
}

fact acyclic {
	no iden & ^(left + right + middle)
}

fact connected {
	some root: Node | Node in root.*(left + right + middle)
}

run {
	some n: TwoThreeNode | n.isInternal
	some n: TwoThreeNode | n.isExternal
	some n: TwoThreeNode | n.isTwoNode
	some n: TwoThreeNode | n.isThreeNode
} for 9 but 3 int
