enum Color {BLACK, RED}

sig Node {
	num: Int,
	left: lone Node,
  	right: lone Node,
	color: one Color,
}

fact btree {
	some r : Node | { 
		Node in r.^(left + right) + r
		r.color = BLACK //root is black
	}
	
	all n : Node | {
		-- no cycles
		n not in n.^(left + right)
		-- at most one parent for each node
		lone n.~(left + right)
	}
	-- distincti children
	no left & right
}

fact orderedTree {       
    all n: Node | {
      (all l: n.left.*(left + right) | n.num > l.num) and
      (all r: n.right.*(left + right) | n.num < r.num)
	}
}

fact redNodeHasTwoBlackChildren {
	all n: Node | {
		(n.color = RED and some n.left) => n.left.color = BLACK
		(n.color = RED and some n.right) => n.right.color = BLACK
	}
}

fact blackHeightIsSameToAllPaths {
  	all e, f : Node |
		(no e.left || no e.right) && (no f.left || no f.right) =>
			#{p : Node | e in p.*(left + right) and p.color = BLACK} = 
			#{p : Node | f in p.*(left + right) and p.color = BLACK}
}

pred show {
	-- can add constraints to see different variations of trees here
	all d: Node.num | d > 0
}

run show for exactly 7 Node
