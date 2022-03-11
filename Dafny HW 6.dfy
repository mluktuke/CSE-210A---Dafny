datatype Tree<T> = Leaf | Node(Tree<T>, Tree<T>, T)
datatype List<T> = Nil | Cons(T, List<T>)

function flatten<T>(tree:Tree<T>):List<T>
{
	match tree
    case Leaf => Nil
    case Node(t, t', root) => Cons(root, append(flatten(t), flatten(t')))
}
//(a1) flatten(Leaf) == Nil
//(a2) flatten(Node(t, t', root)) == Cons(root, append(flatten(t), flatten(t')))

function append<T>(xs:List<T>, ys:List<T>):List<T>
ensures xs == Nil ==> append(xs, ys) == ys
ensures ys == Nil ==> append(xs, ys) == xs
{
	match xs
    case Nil => ys
    case Cons(x, xs') => Cons(x, append(xs',ys))
}
//(a3) append(Nil) == ys
//(a4) append(Cons(x, xs'), ys) == Cons(x, append(xs',ys))

function treeContains<T>(tree:Tree<T>, element:T):bool
{
	match tree
    case Leaf => false
    case Node(t, t', root) => (root == element) || treeContains(t, element) || treeContains(t', element)

}
//(a5) treeContains(Leaf, element) == false
//(a6) treeContains(Node(t, t', root), element) == (root == element) || treeContains(t, element) || treeContains(t', element)

function listContains<T>(xs:List<T>, element:T):bool
{
	match xs
    case Nil => false
    case Cons(x, xs') => 
        if (x == element)
        then true
        else listContains(xs', element)
}
//(a7) listContains(Nil, element) == false
//(a8) listContains(Cons(x, xs'), element) == (x == element) || listContains(xs', element)

lemma sameElements<T>(tree:Tree<T>, element:T)
ensures treeContains(tree, element) <==> listContains(flatten(tree), element)
{
	match tree
    case Leaf => {}
    case Node(t, t', root) => 
    sameElements(t, element);
    sameElements(t', element);
    assert treeContains(t, element) == listContains(flatten(t), element);
    assert treeContains(t', element) == listContains(flatten(t'), element);
    {
        assert treeContains(tree, element)
            == treeContains(Node(t, t', root), element)
            == (root == element) || treeContains(t, element) || treeContains(t', element) //a6
            == (root == element) || listContains(flatten(t), element) || listContains(flatten(t'), element) //IH
            == (root == element) || listContains(append(flatten(t), flatten(t')), element)
            == listContains(Cons(root, append(flatten(t), flatten(t')), element) //a8
            == listContains(flatten(Node(t, t', root)), element) //a2
            == listContains(flatten(tree), element)
            ;
    }
}