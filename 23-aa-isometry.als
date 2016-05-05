--open 2_3_tree2 as tt
open aa-tree as aa

pred isom[a: tt/Node, b: aa/Node] {
}


assert bad {
	some t: tt/Node {
		no n: aa/Node | isom[t, n]
	}
}

run {}
