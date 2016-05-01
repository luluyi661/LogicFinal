abstract sig Node {}

sig twoNode extends Node {
	num: one Int,
	left: lone Node,
	right: lone Node
} {
	no left & right
}

sig threeNode extends Node {
	left3: one twoNode,
	right3: one twoNode
} {
	left3.right = right3.left
	no left3 & right3
	left3.num < right3.num
}

sig fourNode extends Node {
	left4: one twoNode,
	mid4: one twoNode,
	right4: one twoNode
} {
	left4.right = mid4.left
	mid4.right = right4.left
	no left4 & mid4 & right4
	left4.num < mid4.num
	mid4.num < right4.num
}

fact twothreefourtreee {
	-- root reaches everything
	some r : Node |
		Node in r.^(left + right + left3 + right3 + left4 + mid4 + right4) + r

	all n : Node | {
		-- no cycles
		n not in n.^(left + right + left3 + right3 + left4 + mid4 + right4)
		-- at most one parent for each node
		lone n.~(left + right + left3 + right3 + left4 + mid4 + right4)
	}
}

fact orderedTree {       
    all n: twoNode | {
      (all l: n.left.*(left + right + left3 + right3 + left4 + mid4 + right4) | n.num > l.num) and
      (all r: n.right.*(left + right + left3 + right3 + left4 + mid4 + right4) | n.num < r.num)
	}
}

// all leaves are at the same depth
fact leavesSameDepth {
  	all e, f : twoNode |
		(no e.left && no e.right) && (no f.left && no f.right) =>
			#{p : Node | e in p.*(left + right + left3 + right3 + left4 + mid4 + right4)} = 
			#{p : Node | f in p.*(left + right + left3 + right3 + left4 + mid4 + right4)}
}

pred show {
	#{p : twoNode | no p.left && no p.right} > 1
}

run show for 10
