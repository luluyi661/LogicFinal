abstract sig Node {
}

sig twoNode extends Node {
	left2 : lone Node,
	right2 : lone Node
} {
	(some left2 and some right2) or (no left2 and no right2)
	no left2 & right2
}

sig threeNode extends Node {
	left3 : lone Node,
	mid3 : lone Node,
	right3 : lone Node
} {
	(some left3 and some mid3 and some right3) 
	or (no left3 and no mid3 and no right3)
	no left3 & mid3
	no left3 & right3
	no mid3 & right3
}

sig fourNode extends Node {
	left4: lone Node,
	mid_left4 : lone Node,
	mid_right4 : lone Node,
	right4: lone Node
} {
	(some left4 and some mid_left4 and some mid_right4 and some right4) 
	or (no left4 and no mid_left4 and no mid_right4 and no right4)
	no (left4 & mid_left4)
	no (left4 & mid_right4)
	no (left4 & right4)
	no (mid_left4 & mid_right4)
	no (mid_right4 & right4)
	no (mid_left4 & right4)
}

fact twothreefourtreee {
	-- root reaches everything
	some r : Node | {
		Node in r.^(left2 + right2 + left3 + mid3 + right3 + left4 + mid_left4
			+ mid_right4 + right4) + r
	}
	all n : Node | {
		-- no cycles
		n not in n.^(left2 + right2 + left3 + mid3 + right3 + left4 + mid_left4
			+ mid_right4 + right4)
		-- at most one parent for each node
		lone n.~(left2 + right2 + left3 + mid3 + right3 + left4 + mid_left4
			+ mid_right4 + right4)
	}
}

// all leaves are at the same depth
fact leavesSameDepth {
  	all e, f : Node |
		{{(e in twoNode and no e.left2) or
		(e in threeNode and no e.left3) or
		(e in fourNode and no e.left4)}
		and
		{(f in twoNode and no f.left2) or
		(f in threeNode and no f.left3) or
		(f in fourNode and no f.left4)}}
		=>
			#{p : Node | e in p.*(left2 + right2 + left3 + mid3 + right3 + left4 + mid_left4 + mid_right4 + right4)} = 
			#{p : Node | f in p.*(left2 + right2 + left3 + mid3 + right3 + left4 + mid_left4 + mid_right4 + right4)}
}

pred show {
	#Node = 3
}

run show
