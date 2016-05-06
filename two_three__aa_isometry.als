open two_three_tree as tt
open aa_tree as aa

fact noValuesReused {
	all i: Int | {
		lone n: tt/Node | n.a = i or n.b = i
		lone n: aa/Node | n.value = i
	}
}

pred twoNodeIsom[twoNode: tt/TwoThreeNode, aaNode: aa/Node] {
	aaNode.right.level != aaNode.level
	twoNode.a = aaNode.value
	
	twoNode.left.a = aaNode.left.value
	twoNode.right.a = aaNode.right.value
	--isom[twoNode.left, aaNode.left]
	--isom[twoNode.right, aaNode.right]
}

pred threeNodeIsom[threeNode: tt/TwoThreeNode, aaNode: aa/Node] {
	aaNode.right.level = aaNode.level
	
	threeNode.a = aaNode.value
	threeNode.b = aaNode.right.value

	--isom[threeNode.left, aaNode.left]
	--isom[threeNode.middle, aaNode.right.left]
	--isom[threeNode.right, aaNode.right.right]
}

pred isom[ttNode: tt/Node, aaNode: aa/Node] {
	ttNode.isTwoNode => twoNodeIsom[ttNode, aaNode]
	ttNode.isThreeNode => threeNodeIsom[ttNode, aaNode]
	ttNode in tt/Leaf => no aaNode
}


assert bad {
	some t: tt/Node {
		no n: aa/Node | isom[t, n]
	}
}

run {
	some n: tt/TwoThreeNode | n.isTwoNode
	some n: tt/TwoThreeNode | n.isThreeNode

	all ttNode: tt/TwoThreeNode {
		some aaNode: aa/Node | isom[ttNode, aaNode]
	}
} for 10
