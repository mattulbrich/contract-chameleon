package example;

public abstract class TreeNode {

    //@ predicate pred(list<int> absVal);

    public static TreeNode init(int v)
    //@ requires true;
    //@ ensures result.pred(?result_absVal) &*& (result_absVal) == (cons(v, nil));
    {
        //TODO: Implement method 'example.TreeNode.init'.
        return null;
    }

    public abstract void add(int v);
    //@ requires this.pred(?this_absVal_old) &*& true;
    //@ ensures this.pred(?this_absVal) &*& (this_absVal) == (METHOD_APPL);

    public abstract boolean contains(int v);
    //@ requires this.pred(?this_absVal_old) &*& true;
    //@ ensures this.pred(?this_absVal) &*& (result) == (mem(this_absVal, v));
}
