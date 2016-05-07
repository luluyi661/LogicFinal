enum Color {BLACK, RED}

one sig rbt {
	children: set rbtNode	
}

sig rbtNode {
	num: Int,
	left: lone rbtNode,
  	right: lone rbtNode,
	color: one Color,
} {
	left in rbt.children
	right in rbt.children
}

fact btree {
	one r : rbtNode | { 
		rbtNode in r.^(left + right) + r
		r.color = BLACK //root is black
		r in rbt.children
	}
	
	all n : rbtNode | {
		-- no cycles
		n not in n.^(left + right)
		-- at most one parent for each node
		lone n.~(left + right)
	}
	-- distincti children
	no left & right
}

fact orderedTree {       
    all n: rbtNode | {
      (all l: n.left.*(left + right) | n.num > l.num) and
      (all r: n.right.*(left + right) | n.num < r.num)
	}
}

fact redNodeHasTwoBlackChildren {
	all n: rbtNode | {
		(n.color = RED and some n.left) => n.left.color = BLACK
		(n.color = RED and some n.right) => n.right.color = BLACK
	}
}

fact blackHeightIsSameToAllPaths {
  	all e, f : rbtNode |
		(no e.left || no e.right) && (no f.left || no f.right) =>
			#{p : rbtNode | e in p.*(left + right) and p.color = BLACK} = 
			#{p : rbtNode | f in p.*(left + right) and p.color = BLACK}
}

pred show {
	-- can add constraints to see different variations of trees here
	all d: rbtNode.num | d > 0
}

run show for exactly 5 rbtNode
