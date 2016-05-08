module two_three_tree

sig Node {
	parent: lone Node,
	a: Int,
	b: lone Int,
	left: lone Node,
	right: lone Node,
	middle: lone Node
} {
	-- at most one parent
	parent = this.~(@left + @right + @middle)

	-- children are not the same
	no left & right
	no left & middle
	no right & middle

	a != b

	some left iff some right

	-- 3-nodes have 2 values
	some middle iff some b

	-- Internal nodes (nodes with children) only have non-leaf children
	some middle => some left and some right

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

pred Node.isTwoNode {
	no this.middle
}

pred Node.isThreeNode {
	some this.middle
}

pred Node.isExternal {
	no this.(left + right + middle)
}

pred Node.isInternal {
	some this.(left + right + middle)
}

fact acyclic {
	no iden & ^(left + right + middle)
}

fact connected {
	one root: Node | no root.parent
}

fun tree_root: Node {
	{r: Node | no r.parent}
}

run {
	some n: Node | n.isInternal
	some n: Node | n.isExternal
	some n: Node | n.isTwoNode
	some n: Node | n.isThreeNode
} for 9 but 3 int
