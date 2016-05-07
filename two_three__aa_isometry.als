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

	some twoNode.left iff some aaNode.left
	some twoNode.right iff some aaNode.right
	
	--twoNode.left.a = aaNode.left.value
	--twoNode.right.a = aaNode.right.value
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

pred isom[ttNode: tt/TwoThreeNode, aaNode: aa/Node] {
	ttNode.isTwoNode => twoNodeIsom[ttNode, aaNode]
	ttNode.isThreeNode => threeNodeIsom[ttNode, aaNode]
	--ttNode in tt/Leaf => no aaNode
}

pred allIsometric {
	all ttNode: tt/TwoThreeNode | some aaNode: aa/Node | isom[ttNode, aaNode]
}

assert nothingIsometric_unsat {
	--some ttNode: tt/TwoThreeNode | no aaNode: aa/Node | isom[ttNode, aaNode]
	--no ttNode: tt/TwoThreeNode | no aaNode: aa/Node | isom[ttNode, aaNode]
	allIsometric
}

assert isometricInRightPlace {
	-- Use implies here because otherwise Alloy can make this vacuously false by 
	-- not including the isometry for some nodes
	allIsometric implies
	all t: tt/Node - tt/tree_root, a: aa/Node - aa/tree_root | {
		isom[t, a] => {
			isom[t.~(left + right + middle), a.~(left + right)]
			some t.left => isom[t.left, a.left]
		}

		--some t.left => isom[t.left, a.left]
		-- TODO: check right
		-- or does the parent check cover it?
		-- maybe use alloy to find out
	}
}

assert isometricParentCheckEnough {
	all t: tt/Node - tt/tree_root, a: aa/Node - aa/tree_root | {
		isom[t, a] => isom[t.~(left + right + middle), a.~(left + right)]
	} implies all t: tt/Node, a: aa/Node | {
		isom[t, a] => isom[t.left, a.left]
	}
}

check isometricParentCheckEnough

check isometricInRightPlace

check nothingIsometric_unsat

run {
	some n: tt/TwoThreeNode | n.isThreeNode

	tt/TwoThreeNode.(a + b) = aa/Node.value

	allIsometric
} for 10
