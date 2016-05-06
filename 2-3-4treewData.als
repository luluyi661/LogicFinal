open redblacktree as RBT

abstract sig Node {
}

sig twoNode extends Node {
	left2 : lone Node,
	right2 : lone Node,
	num2: one Int
} {
	(some left2 and some right2) or (no left2 and no right2)
	no left2 & right2
	num2 > 0
}

sig threeNode extends Node {
	left3 : lone Node,
	mid3 : lone Node,
	right3 : lone Node,
	num3_left : one Int,
	num3_right : one Int
} {
	(some left3 and some mid3 and some right3) 
	or (no left3 and no mid3 and no right3)
	no left3 & mid3
	no left3 & right3
	no mid3 & right3
	num3_left < num3_right
	num3_left > 0
}

sig fourNode extends Node {
	left4: lone Node,
	mid_left4 : lone Node,
	mid_right4 : lone Node,
	right4: lone Node,
	num4_left : one Int,
	num4_mid : one Int,
	num4_right : one Int
} {
	(some left4 and some mid_left4 and some mid_right4 and some right4) 
	or (no left4 and no mid_left4 and no mid_right4 and no right4)
	no (left4 & mid_left4)
	no (left4 & mid_right4)
	no (left4 & right4)
	no (mid_left4 & mid_right4)
	no (mid_right4 & right4)
	no (mid_left4 & right4)
	num4_left < num4_mid
	num4_mid < num4_right
	num4_left > 0
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

fact orderedTree {       
    all n: twoNode | {
      	(all l: n.left2.*(left2 + right2 + left3 + mid3 + right3 + left4 + mid_left4 + mid_right4 + right4) | 
			{l in twoNode => n.num2 > l.num2
			 l in threeNode => n.num2 > l.num3_right
			 l in fourNode => n.num2 > l.num4_right
			}) and 
		(all r: n.right2.*(left2 + right2 + left3 + mid3 + right3 + left4 + mid_left4 + mid_right4 + right4) | 
			{r in twoNode => n.num2 < r.num2
			 r in threeNode => n.num2 < r.num3_left
			 r in fourNode => n.num2 < r.num4_left
			})
	}

	all n: threeNode | {
		(all l: n.left3.*(left2 + right2 + left3 + mid3 + right3 + left4 + mid_left4 + mid_right4 + right4) | 
			{l in twoNode => n.num3_left > l.num2
			 l in threeNode => n.num3_left > l.num3_right
			 l in fourNode => n.num3_left > l.num4_right
			}) and 
		(all r: n.right3.*(left2 + right2 + left3 + mid3 + right3 + left4 + mid_left4 + mid_right4 + right4) | 
			{r in twoNode => n.num3_right < r.num2
			 r in threeNode => n.num3_right < r.num3_left
			 r in fourNode => n.num3_right < r.num4_left
			}) and
		(all m: n.mid3.*(left2 + right2 + left3 + mid3 + right3 + left4 + mid_left4 + mid_right4 + right4) | 
			{m in twoNode => (n.num3_right > m.num2 and n.num3_left < m.num2)
			 m in threeNode => (n.num3_right > m.num3_right and n.num3_left < m.num3_left)
			 m in fourNode => (n.num3_right > m.num4_right and n.num3_left < m.num4_left)
			})
	}

	all n: fourNode | {
		(all l: n.left4.*(left2 + right2 + left3 + mid3 + right3 + left4 + mid_left4 + mid_right4 + right4) | 
			{l in twoNode => n.num4_left > l.num2
			 l in threeNode => n.num4_left > l.num3_right
			 l in fourNode => n.num4_left > l.num4_right
			}) and 
		(all r: n.right4.*(left2 + right2 + left3 + mid3 + right3 + left4 + mid_left4 + mid_right4 + right4) | 
			{r in twoNode => n.num4_right < r.num2
			 r in threeNode => n.num4_right < r.num3_left
			 r in fourNode => n.num4_right < r.num4_left
			}) and
		(all ml: n.mid_left4.*(left2 + right2 + left3 + mid3 + right3 + left4 + mid_left4 + mid_right4 + right4) | 
			{ml in twoNode => (n.num4_mid > ml.num2 and n.num4_left < ml.num2)
			 ml in threeNode => (n.num4_mid > ml.num3_right and n.num4_left < ml.num3_left)
			 ml in fourNode => (n.num4_mid > ml.num4_right and n.num4_left < ml.num4_left)
			}) and
		(all mr: n.mid_right4.*(left2 + right2 + left3 + mid3 + right3 + left4 + mid_left4 + mid_right4 + right4) | 
			{mr in twoNode => (n.num4_right > mr.num2 and n.num4_mid < mr.num2)
			 mr in threeNode => (n.num4_right > mr.num3_right and n.num4_mid < mr.num3_left)
			 mr in fourNode => (n.num4_right > mr.num4_right and n.num4_mid < mr.num4_left)
			})
	}
}

pred show {
	add[#threeNode, mul[2, #fourNode]] = #{n : RBT/rbtNode | n.color = RED}
	add[add[#twoNode, mul[2, #threeNode]], mul[3, #fourNode]] = #RBT/rbtNode
	add[add[#twoNode, #threeNode], #fourNode] = #{n : RBT/rbtNode | n.color = BLACK}
	all n: twoNode | {
		some rbt : RBT/rbtNode | {
			rbt.num = n.num2
			some rbt.left => rbt.left.color = BLACK
			some rbt.right => rbt.right.color = BLACK
		}
	}
	all n: threeNode | {
		some rbt1 : RBT/rbtNode | rbt1.num = n.num3_left
		some rbt2: RBT/rbtNode | rbt2.num = n.num3_right
	}
	all n: fourNode | {
		some rbt1 : RBT/rbtNode | rbt1.num = n.num4_left and rbt1.color = RED
		some rbt2: RBT/rbtNode | rbt2.num = n.num4_mid
		some rbt3: RBT/rbtNode | rbt3.num = n.num4_right and rbt3.color = RED
	}
	#twoNode > 0
	
}

run show for 6
