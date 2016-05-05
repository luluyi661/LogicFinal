open util/ordering [Data]

sig Data {}

abstract sig Node {} {
	--lone parent: Node | this in parent.(TwoNode <: left + ThreeNode <: left + TwoNode <: right + ThreeNode <: right + middle)
}

fact onlyOneParent {
	/*
	no n: Node | {
		some disj p1, p2: Node | {
			p1 -> n in TwoNode <: left + ThreeNode <: left + TwoNode <: right + ThreeNode <: right + middle
			p2 -> n in TwoNode <: left + ThreeNode <: left + TwoNode <: right + ThreeNode <: right + middle
		}
	}
	*/
	all n: Node | {
		lone n.~(TwoNode <: left + ThreeNode <: left + TwoNode <: right + ThreeNode <: right + middle)
	}
}

sig TwoNode extends Node {
	a: Data,
	left: Node,
	right: Node
} {
	no left & right
	
	-- TODO: same height
}

sig ThreeNode extends Node {
	a: Data,
	b: Data,
	left: Node,
	right: Node,
	middle: Node
} {
	no left & right
	no left & middle
	no right & middle

	-- TODO: same height
}

fact noSelfLoops {
	no iden & TwoNode <: left
	no iden & ThreeNode <: left
	no iden & TwoNode <: right
	no iden & ThreeNode <: right
	no iden & middle
}

sig Leaf extends Node {}

pred isValid2Node[n: TwoNode] {
	is23Tree[n.left]
	is23Tree[n.right]
	all e: elements[n.left] | n.a.gt[e]
	all e: elements[n.right] | n.a.lte[e]
}

pred isValid3Node[n: ThreeNode] {
	is23Tree[n.left]
	is23Tree[n.right]
	is23Tree[n.middle]

	all e: elements[n.left] | n.a.gt[e]
	all e: elements[n.middle] | n.a.lte[e] and n.b.gt[e]
	all e: elements[n.right] | n.b.lte[e]
}

pred is23Tree[n: Node] {
	n in TwoNode => isValid2Node[n]
	
	n in ThreeNode => isValid3Node[n]
}

fun contents[n: Node] : set Node {
	n + n.^(TwoNode <: left) + n.^(ThreeNode <: left) + n.^(TwoNode <: right) + n.^(ThreeNode <: right) + n.^middle
}

fun elements[n: Node] : set Data {
	let c = contents[n] | {
		c.(TwoNode <: a) + c.(ThreeNode <: a) + c.b
	}
}

fun data[n: Node] : set Data {
	n.(TwoNode <: a) + n.(ThreeNode <: a) + n.b
}

fact connected {
	some n: Node | Node in contents[n]
}

pred interesting {
	some TwoNode
	some ThreeNode
}

run {
	some n: Node | is23Tree[n]
	interesting
} for 10 but 3 int
