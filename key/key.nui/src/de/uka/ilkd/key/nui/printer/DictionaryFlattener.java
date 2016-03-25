/**
 * 
 */
package de.uka.ilkd.key.nui.printer;

import java.util.ArrayList;
import java.util.EmptyStackException;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.TreeSet;

import de.uka.ilkd.key.nui.util.NUIConstants;
import de.uka.ilkd.key.util.Pair;

/**
 * The Flattener converts the Multidimensional Maps of the
 * {@link PrintDictionary} into a one dimensional {@link List}
 * 
 * @author Maximilian Li
 */
public class DictionaryFlattener {
    private List<Pair<Integer, String>> flattenedTagList = null;
    private Stack<Pair<Integer, String>> tagStack;

    /**
     * flattens the DictionaryMaps into lists
     * 
     * @param openMap
     *            a Map of the opening Tags
     * @param closeMap
     *            a Map of the Closing Tags
     * @return a List of {@link Pair}s consisting of Index and InsertionTag
     */
    // 2 separate LoopPhases for Tag Applying, to avoid self canceling and slim
    // down amount of tags.
    protected List<Pair<Integer, String>> flatten(
            Map<Integer, Map<Integer, List<String>>> openMap,
            Map<Integer, Map<Integer, List<String>>> closeMap) {
        Set<Integer> keySet = new TreeSet<>();
        keySet.addAll(openMap.keySet());
        keySet.addAll(closeMap.keySet());

        flattenedTagList = new ArrayList<>();
        tagStack = new Stack<>();

        for (Integer i : keySet) {
            // Flatten CloseTags Structure
            if (closeMap.containsKey(i)) {
                flattenTagsMap(i, closeMap, false);
            }
            // Flatten OpenTags Structure
            if (openMap.containsKey(i)) {
                flattenTagsMap(i, openMap, true);
            }
        }
        return flattenedTagList;
    }

    /**
     * flattens a single map entry depending on if it is the openTag or closeTag
     * Map
     * 
     * @param i
     *            the key index of the Map
     * @param map
     *            the map to be flattened
     * @param open
     *            a boolean value signaling if this is the openTagsMap
     */
    private void flattenTagsMap(int i,
            Map<Integer, Map<Integer, List<String>>> map, boolean open) {
        List<String> insertTagList;
        Stack<Pair<Integer, String>> saveTagStack = new Stack<>();
        int prio;
        for (int j = 0; j < HighlightType.values().length; j++) {
            if (open) {
                prio = j;
            }
            else {
                prio = (HighlightType.values().length - 1) - j;
            }
            insertTagList = map.get(i).get(prio);
            if (insertTagList == null)
                continue;
            for (String insertTag : insertTagList) {
                if (insertTag == null || insertTag.isEmpty())
                    continue;

                // Correctly Prioritize even inside other spans
                buildSaveStack(i, prio, open, saveTagStack);
                if (open) {
                    tagStack.push(new Pair<Integer, String>(j, insertTag));
                }
                else {
                    try {
                        tagStack.pop();
                    }
                    catch (EmptyStackException e) {
                        System.err.println("Could not make insertTagList.\n"
                                + "This is caused by having incomplete Pairs of tags, \n"
                                + "or trying to insert a tagPair, where the closeTag is before the openTag.");
                    }

                }

                insertTagAndSaves(i, insertTag, saveTagStack);
            }
        }
    }

    /**
     * inserts the insertTag into the resultList and empties the saveTagStack
     * 
     * @param i
     *            the index of the insertTag
     * @param insertTag
     *            the tag to be inserted
     * @param saveTagStack
     *            the stack saving formerly removed Tags, that should be
     *            inserted again
     */
    private void insertTagAndSaves(int i, String insertTag,
            Stack<Pair<Integer, String>> saveTagStack) {
        flattenedTagList.add(new Pair<Integer, String>(i, insertTag));
        emptySaveStack(i, saveTagStack);
    }

    /**
     * builds a {@link Stack} holding the Tags that are cut off, to avoid
     * overlapping of tags
     * 
     * @param i
     *            the index of current operation
     * @param prio
     *            the prioritylevel of the insertiontag of this operation
     * @param buildOpenTags
     *            a boolean signifying if the current operation is for an
     *            opening tag
     * @param saveTagStack
     *            the {@link Stack} for saving purposes
     */
    private void buildSaveStack(int i, int prio, boolean buildOpenTags,
            Stack<Pair<Integer, String>> saveTagStack) {

        while (!tagStack.isEmpty()
                && ((tagStack.peek().first > prio && buildOpenTags)
                        || tagStack.peek().first != prio && !buildOpenTags)) {
            flattenedTagList.add(
                    new Pair<Integer, String>(i, NUIConstants.CLOSING_TAG));
            saveTagStack.push(tagStack.pop());
        }
    }

    /**
     * empties the saving {@link Stack} and inserts its contents into the
     * resultList again
     * 
     * @param i
     *            the index of the current operation
     * @param saveTagStack
     *            the {@link Stack} for saving purposes
     */
    private void emptySaveStack(int i,
            Stack<Pair<Integer, String>> saveTagStack) {

        while (saveTagStack.size() > 0) {
            flattenedTagList.add(
                    new Pair<Integer, String>(i, saveTagStack.peek().second));
            tagStack.push(saveTagStack.pop());
        }
    }
}
