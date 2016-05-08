open two_three_tree as tt
open aa_tree as aa

-- By ensuring that any given value is only used once per tree, we effectively make nodes uniquely
-- identifiable, which is how we can check for isometry locally without recurring through the tree.

fact noValuesReused {
	all i: Int | {
		lone n: tt/Node | n.a = i or n.b = i
		lone n: aa/Node | n.value = i
	}
}

-- By ensuring that both kinds of trees have the same set of values, we can avoid some
-- kinds of spurious counterexample where Alloy merely adds nodes with different values to one
-- kind of tree. This is acceptable because we know there won't be an isometry between tree
-- representations with different values, so it's not worth considering them.

fact sameData {
	tt/Node.(a + b) = aa/Node.value
}

-- Splitting our isometry predicate into cases makes it slightly cleaner to read (it started
-- as a failed attempt into tricking Alloy into allowing more recursion).

pred twoNodeIsom[twoNode: tt/Node, aaNode: aa/Node] {
	aaNode.right.level != aaNode.level
	twoNode.a = aaNode.value

	some twoNode.left iff some aaNode.left
	some twoNode.right iff some aaNode.right
}

pred threeNodeIsom[threeNode: tt/Node, aaNode: aa/Node] {
	aaNode.right.level = aaNode.level
	
	threeNode.a = aaNode.value
	threeNode.b = aaNode.right.value

	some threeNode.left iff some aaNode.left
	some threeNode.middle iff some aaNode.right.left
	some threeNode.right iff some aaNode.right.right
}

pred isom[ttNode: tt/Node, aaNode: aa/Node] {
	ttNode.isTwoNode => twoNodeIsom[ttNode, aaNode]
	ttNode.isThreeNode => threeNodeIsom[ttNode, aaNode]
}

pred allIsometric {
	all ttNode: tt/Node | some aaNode: aa/Node | isom[ttNode, aaNode]
}

assert isometricInRightPlace {
	-- Verify that our approach of checking values and structure at the individual node level
	-- carries over to the entire tree. This isn't verifying that the isometry itself generally
	-- applies, just that it's equivalent to check it locally to avoid recursion.

	-- If every 2-3 node has a corresponding AA node, isometric nodes should be connected to nodes
	-- that are also isometric (because each value is used once, nodes are effectively unique). The
	-- intuition is that finding 2-3 and AA trees for the same values such that individual nodes
	-- are isometric forces the overall trees to be isometric, so we can use that approach to verify
	-- the existence of an isometry between the trees.

	-- Use `implies allIsometric` here because otherwise Alloy can find spurious counterexamples by 
	-- not including the isometry for some nodes.
	allIsometric implies {
		all t: tt/Node - tt/tree_root, a: aa/Node - aa/tree_root | {
			isom[t, a] => isom[t.parent, a.parent]
		}
	}
}

assert isometricParentCheckEnough {
	-- Show that making sure isometry between nodes implies isometry between parents is equivalent to
	-- making sure isometry between nodes extends in all directions.
	allIsometric implies {
		all t: tt/Node - tt/tree_root, a: aa/Node - aa/tree_root | {
			isom[t, a] => isom[t.parent, a.parent]
		} iff all t: tt/Node, a: aa/Node | {
			isom[t, a] => {
				-- `some` constraints here are simpler than making `isom` handle empty sets.

				-- In all cases, left children are isometric
				some t.left => isom[t.left, a.left]
				
				-- Right and middle children should also be isometric, but what the right/middle children
				-- are isometric to in the AA tree depends on whether it's a 2-node or a 3-node.
				t.isTwoNode and some t.right => isom[t.right, a.right]
				t.isThreeNode and some t.middle => isom[t.middle, a.right.left] and isom[t.right, a.right.right]
			}
		}
	}
}

check isometricParentCheckEnough

check isometricInRightPlace

check alwaysAllIsometric {
	-- Using the constraint that both trees have the same data as a generator axiom of sorts,
	-- use allIsometric as an unbounded universal quantifier
	allIsometric
}

run interestingIsometric {
	some n: tt/Node | n.isThreeNode
	allIsometric
} for 10
