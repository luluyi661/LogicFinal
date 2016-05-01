open util/ordering [Data]

sig Data {}

abstract sig Node {}

sig TwoNode extends Node {
	a: Data,
	left2: Node,
	right2: Node
} {
	/*
	all n: contents[left] | {
		a.gt[data[n]]
	}

	all n: contents[right] | {
		a.lte[data[n]]
	}
	*/

	-- TODO: same height
}

sig ThreeNode extends Node {
	a: Data,
	b: Data,
	left3: Node,
	right3: Node,
	middle3: Node
} {
	-- TODO: same height

	/*
	all n: contents[left] | {
		a.gt[data[n]]
	}

	all n: contents[middle] | {
		a.lte[data[n]]
		b.gt[data[n]]
	}

	all n: contents[right] | {
		b.lte[data[n]]
	}
	*/
}

fact noSelfLoops {
	no iden & left2
	no iden & right2
	no iden & left3
	no iden & right3
	no iden & middle3
}

sig Leaf extends Node {}

pred is23Tree[n: Node] {
	n in TwoNode => {
		is23Tree[n.left2]
		is23Tree[n.right2]
		all e: elements[n.left2] | n.(TwoNode <: a).gt[e]
		all e: elements[n.right2] | n.(TwoNode <: a).lte[e]
	}
	
	n in ThreeNode => {
		is23Tree[n.left3]
		is23Tree[n.right3]
		is23Tree[n.middle3]
		
		all e: elements[n.left3] | n.(ThreeNode <: a).gt[e]
		all e: elements[n.middle3] | n.(ThreeNode <: a).lte[e] and n.b.gt[e]
		all e: elements[n.right3] | n.b.lte[e]
	}
}

fun contents[n: Node] : set Node {
	n + n.^left2 + n.^left3 + n.^right2 + n.^right3 + n.^middle3
}

fun elements[n: Node] : set Data {
	let c = contents[n] | {
		c.(TwoNode <: a) + c.(ThreeNode <: a) + c.b
	}
}

fun data[n: Node] : set Data {
	n.(TwoNode <: a) + n.(ThreeNode <: a) + n.b
}

run is23Tree for 5
