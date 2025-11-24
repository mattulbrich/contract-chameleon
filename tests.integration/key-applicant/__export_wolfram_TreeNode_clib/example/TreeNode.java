package example;

public abstract class TreeNode {

    //@ public instance ghost \locset footprint;


    //@ public instance invariant \subset(this.*, this.footprint);


    //@ public instance accessible \inv : footprint;


    //@ public instance ghost \dl_set absVal;


    /*@  normal_behavior
        requires (false | true);
        ensures (true & (true ==> \result.absVal == \dl_finiteSetSingleton(v)));
        ensures \fresh(\result.footprint);
        */
    public static TreeNode init(int v) {
        //NOTE: This should be never called, as it is only the interface!
        return null;
    }

    /*@  normal_behavior
        requires (false | true);
        ensures (true & (true ==> (\forall int x;\dl_finiteSetMember(\old(this.absVal), x) || x == v) && \dl_finiteSetMember(this.absVal, v)));
        accessible this.footprint;
        assignable this.footprint;
        */
    public abstract void add(int v);

    /*@  normal_behavior
        requires (false | true);
        ensures (true & (true ==> \result == \dl_finiteSetMember(this.absVal, v)));
        accessible this.footprint;
        assignable this.footprint;
        */
    public abstract boolean contains(int v);
}
