package example;

public class TreeNodeImpl extends TreeNode {

    //@ predicate pred(list<int> absVal);

    public void add(int v)
    //@ requires this.pred(?this_absVal_old) &*& true;
    //@ ensures this.pred(?this_absVal) &*& (this_absVal) == (METHOD_APPL);
    {
        //TODO: Implement method 'example.TreeNode.add'.
    }

    public boolean contains(int v)
    //@ requires this.pred(?this_absVal_old) &*& true;
    //@ ensures this.pred(?this_absVal) &*& (result) == (mem(this_absVal, v));
    {
        //TODO: Implement method 'example.TreeNode.contains'.
        return false;
    }
}
