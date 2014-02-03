package com.csvanefalk.keytestgen.targetmodels.own;

/**
 * Created by christopher on 17/01/14.
 */
public class Simple {
    public int l;
    private int h;

    /*@ public normal_behavior
     @ ensures \old(l) <l;
     @*/
    public void magic() {
        if (h > 0) { l = l + 1; } else { l = l + 2; }
    }

    public void magic2(int h, int l) {
        if (h > 0) {
            l = l + 1;
        } else { l = l + h; }
    }

    public void magic3(int h, int l) {
        if (h < 5) {
            l = l + 1;
        } else { l = l + h; }
    }
}