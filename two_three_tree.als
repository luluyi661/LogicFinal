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
	
	-- The value constraints that make this a binary search tree would normally be enforced
	-- during insertion, but since that's not being modeled, we make them facts here.

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
	no this.b
}

pred Node.isThreeNode {
	some this.b
}

pred Node.isExternal {
	no this.(left + right + middle)
}

pred Node.isInternal {
	some this.(left + right + middle)
}

pred Node.isLeaf {
	no this.(left + right + middle)
}

fact acyclic {
	no iden & ^(left + right + middle)
}

fact connected {
	one root: Node | no root.parent
}

fact distinctValues {
	all disj n1, n2: Node | {
		no n1.(a + b) & n2.(a + b)
	}
}

fun tree_root: Node {
	{r: Node | no r.parent}
}

-- Three core properties:
-- 1. All internal nodes are 2-nodes or 3-nodes: This is a consequence of
--    how the tree is structured, since there's nothing else for the nodes to be.
-- 2. All leaves are at the same level: See assertion below
-- 3. All data is kept in sorted order, so forming a list by appending n.left, n.a, n.middle, n.b, n.right
--    recursively would produce a sorted list. This gets ugly in Alloy, so we check it locally in the
--    assertion below.

assert leavesAtSameLevel {
	all disj leaf1, leaf2: Node | {
		leaf1.isLeaf and leaf2.isLeaf implies {
			#{leaf1.^~(left + right + middle)} = #{leaf2.^~(left + right + middle)}
		}
	}
}

assert sortedOrder {
	all n: Node {
		n.isInternal implies {
			n.a > n.left.(a + b)
			n.a < n.right.(a + b)
			n.isThreeNode implies {
				n.b > n.left.(a + b)
				n.b < n.left.(a + b)
			
				n.b > n.middle.(a + b)
				n.a < n.middle.(a + b)
			}
		}
	}
}

check leavesAtSameLevel

check sortedOrder

run {
	some n: Node | n.isInternal
	some n: Node | n.isExternal
	some n: Node | n.isTwoNode
	some n: Node | n.isThreeNode
} for 9
