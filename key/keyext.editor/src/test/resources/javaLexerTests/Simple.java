class For implements Iterable {
    int[] a; /*
    */ Trivial it; // Line comment
    For f;

    int sum () {
        int s = 0;
        int z = a.length;
        /*
        Comment
         */
        for (int i: a) s+= i;
        return s;
    }
}
