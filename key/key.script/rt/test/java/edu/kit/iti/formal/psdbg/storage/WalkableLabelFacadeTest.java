package edu.kit.iti.formal.psdbg.storage;

import javafx.util.Pair;
import org.junit.Assert;
import org.junit.Test;

import java.util.Collection;
import java.util.Collections;
import java.util.List;

import static edu.kit.iti.formal.psdbg.storage.WalkableLabelFacade.*;
import static java.util.Arrays.asList;

/**
 * @author Alexander Weigl
 * @version 1 (16.05.18)
 */
public class WalkableLabelFacadeTest {
    @Test
    public void testParseUncompressed() {
        Collection<Integer> v1 = parseUncompressed("[0,1,2,3,4,0,1,2,3,4]", PREFIX_WALKABLE_LABEL, SUFFIX_WALKABLE_LABEL, ENTRY_DELIMITER, Integer::parseInt);
        Collection<Integer> v2 = parseUncompressed("[]", PREFIX_WALKABLE_LABEL, SUFFIX_WALKABLE_LABEL, ENTRY_DELIMITER, Integer::parseInt);
        Collection<Integer> v3 = parseUncompressed("[-111]", PREFIX_WALKABLE_LABEL, SUFFIX_WALKABLE_LABEL, ENTRY_DELIMITER, Integer::parseInt);
        Collection<Integer> v4 = parseUncompressed("]", PREFIX_WALKABLE_LABEL, SUFFIX_WALKABLE_LABEL, ENTRY_DELIMITER, Integer::parseInt);
        Collection<Integer> v5 = parseUncompressed("", PREFIX_WALKABLE_LABEL, SUFFIX_WALKABLE_LABEL, ENTRY_DELIMITER, Integer::parseInt);

        Assert.assertEquals(asList(0, 1, 2, 3, 4, 0, 1, 2, 3, 4), v1);
        Assert.assertEquals(Collections.emptyList(), v2);
        Assert.assertEquals(asList(-111), v3);
        Assert.assertEquals(Collections.emptyList(), v4);
        Assert.assertEquals(Collections.emptyList(), v5);
    }

    @Test
    public void testCompression() {
        List<Integer> list = asList(0, 0, 0, 0, 1, 1, 1, 1, 1, 10, 0, 0, 1, 1, 1, 10, 0, 2, 2, 4);
        List<Integer> list1 = Collections.singletonList(0);
        List<Integer> list0 = Collections.emptyList();
        List<Integer> list2 = asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1);

        compressAndUncompress(list);
        compressAndUncompress(list1);
        compressAndUncompress(list0);
        compressAndUncompress(list2);

        System.out.println(compress(list.iterator()));
        System.out.println(compress(list1.iterator()));
        System.out.println(compress(list2.iterator()));
        System.out.println(compress(list0.iterator()));

        Assert.assertEquals(
                "[4=0, 5=1, 1=10, 2=0, 3=1, 1=10, 1=0, 2=2, 1=4]",
                compress(list.iterator()).toString());

        Assert.assertEquals("[1=0]", compress(list1.iterator()).toString());
        Assert.assertEquals("[16=1]", compress(list2.iterator()).toString());
        Assert.assertEquals("[]", compress(list0.iterator()).toString());
    }

    public void compressAndUncompress(List<Integer> list) {
        Collection<Pair<Integer, Integer>> clist = compress(list.iterator());
        Collection<Integer> uclist = uncompress(clist.iterator());
        Assert.assertEquals(list, uclist);
    }
}