module aa_tree

open util/integer

sig Node {
	parent: lone Node,
	level: Int,
	left: lone Node,
	right: lone Node,
	value: Int
} {
	no left & right

	parent = this.~(@left + @right)
}

pred Node.hasHorizontalLink {
	this.level = this.right.level
}

-- Makes things a bit easier to work through visually
fact noDuplicateValues {
	all disj n1, n2: Node | n1.value != n2.value
}

fact leavesLevel1 {
	all n: Node | {
		no n.left and no n.right => n.level = 1
	}
}

fact leftChildLevelOneLess {
	all n: Node | {
		some n.left => n.left.level = sub[n.level, 1]
	}
}

fact rightChildLevelAtMostOneLess {
	all n: Node | {
		some n.right => n.right.level = n.level or n.right.level = sub[n.level, 1]
	}
}

fact rightGrandchildLevelLess {
	all n: Node | {
		some n.right.left => n.right.left.level < n.level
		some n.right.right => n.right.right.level < n.level
	}
}

fact nonLeavesHaveChildren {
	all n: Node | {
		n.level > 1 => some n.left and some n.right
	}
}

fact connected {
	one n: Node | no n.parent
}

fun tree_root: Node {
	{r: Node | no r.parent}
}

-- This would normally be a consequence of insertion, which we're not modeling.
pred binaryTree[n: Node] {
	all e: n.left.*(left + right).value | n.value > e
	all e: n.right.*(left + right).value | n.value < e
}

fact allBinaryTrees {
	all n: Node | binaryTree[n]
}

pred interesting {
	some n: Node | n.level > 2
	some n: Node | n.hasHorizontalLink
}

-- The other invariants are sig facts on Node needed to maintain / define structure.

check noLeftRedNodes {
	-- Horizontal links in AA trees are analagous to red links in red-black trees,
	-- and are only allowed to right children. 
	no n: Node | n.left.level = n.level
}


check noConsecutiveHorizontalLinks {
	-- This ought to be a consequence of the rightGrandchildLevelLess fact, but
	-- this assertion is to verify it in a more intuitive format.
	no n: Node | n.hasHorizontalLink and n.right.hasHorizontalLink
}

run interesting for 8
