class A {
    //@ ensures \result;
    boolean m(boolean b) {
        if(b) {
            //! ignore
            return false;
        } else {
            return true;
        }
        return false;
    }
}

