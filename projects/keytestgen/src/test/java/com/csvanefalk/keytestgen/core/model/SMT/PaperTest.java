package com.csvanefalk.keytestgen.core.model.SMT;

import java.util.HashMap;

public class PaperTest {

    public static final HashMap<String, Long> map = new HashMap<String, Long>();

    public static void addResult(String key, Long res) {
        Long previous = map.get(key);
        if (previous == null) {
            previous = 0L;
        }
        Long newVal = previous + res;
        map.put(key, newVal);
       /*
        System.out.println(key + " : " + res);
        System.out.println(key + " : " + map.get(key));
        System.out.println();
        */
    }

    public static void printResults() {
        for (String key : map.keySet()) {
            System.out.println(key + " : " + map.get(key));
        }
    }
}
