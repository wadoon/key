package org.key_project.util.collection;

import static org.junit.Assert.assertEquals;

import java.util.Iterator;
import java.util.Random;

import org.junit.Test;
// import static org.junit.Assert.*;
public class TestImmutableTrieSet {

    @Test
    public void testLargeOps() {

        ImmutableSet<Integer> trie = ImmutableTrieSet.empty();
        ImmutableSet<Integer> def = DefaultImmutableSet.nil();

        Random r = new Random(10);
        for(int i = 0; i < 10000; i++) {
            int nextInt = r.nextInt(1000);
            boolean mode = r.nextBoolean();
            if(mode) {
                trie = trie.add(nextInt);
                def = def.add(nextInt);
            } else {
                trie = trie.remove(nextInt);
                def = def.remove(nextInt);
            }

            assertEquals(trie, def);
            Iterator<Integer> it1 = trie.iterator();
            Iterator<Integer> it2 = def.iterator();
            while(it1.hasNext() && it2.hasNext()) {
                assertEquals(it1.next(), it2.next());
            }
            assertEquals(it1.hasNext(), it2.hasNext());
        }

    }

//    @Test
    public void testTime() throws Exception {
        for (int i = 0; i < 20; i++) {
            time(DefaultImmutableSet.<Integer>nil(), i);
            time(ImmutableTrieSet.<Integer>empty(), i);
        }
    }

    public void time(ImmutableSet<Integer> set, int seed) throws Exception {
        Random r = new Random(seed);
        long now = System.currentTimeMillis();
        for(int i = 0; i <30000; i++) {
            int nextInt = r.nextInt(30000);
            boolean mode = true; r.nextBoolean();
            if(mode) {
                set = set.add(nextInt);
            } else {
                set = set.remove(nextInt);
            }
        }
        System.out.println(System.currentTimeMillis() - now);
    }

}
