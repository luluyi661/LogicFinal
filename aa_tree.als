module aa_tree

open util/ordering [Data]

sig Data {}

sig Node {
	level: Int,
	left: lone Node,
	right: lone Node,
	value: Data
} {
	no left & right

	lone parent: Node | this in parent.(@left + @right)
}

fact leavesLevel1 {
	all n: Node | {
		no n.left and no n.right iff n.level = 1 -- TODO: should this be implies?
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

fact someRoot {
	some n: Node | Node in n + n.^(left + right)
}

pred binaryTree[n: Node] {
	all e: n.^left.value | n.value.gt[e]
	all e: n.^right.value | n.value.lte[e]
}

pred interesting {
	some n: Node | n.level > 2
	some n: Node | n.level = n.right.level
	all d: Data | lone n: Node | n.value = d
}

run {
	all n: Node | binaryTree[n]
	interesting
} for 10 but 5 int
