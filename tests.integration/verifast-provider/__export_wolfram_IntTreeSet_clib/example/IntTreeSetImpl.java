package example;

public class IntTreeSetImpl extends IntTreeSet {

    //@ predicate pred(list<int> absVal);

    public void add(int v)
    //@ requires this.pred(?this_absVal_old) &*& true;
    //@ ensures this.pred(?this_absVal) &*& helper_predicate(v, this_absVal_old, v, this_absVal, ?helper_predicate_res) &*& (helper_predicate_res) && (mem(this_absVal, v));
    {
        //TODO: Implement method 'example.IntTreeSet.add'.
    }

    public boolean contains(int v)
    //@ requires this.pred(?this_absVal_old) &*& true;
    //@ ensures this.pred(?this_absVal) &*& (result) == (mem(this_absVal, v));
    {
        //TODO: Implement method 'example.IntTreeSet.contains'.
        return false;
    }
}
