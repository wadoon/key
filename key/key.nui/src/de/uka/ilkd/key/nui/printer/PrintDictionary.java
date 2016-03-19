/**
 * 
 */
package de.uka.ilkd.key.nui.printer;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.TreeSet;

import de.uka.ilkd.key.nui.util.NUIConstants;
import de.uka.ilkd.key.util.Pair;

/**
 * @author Maximilian Li
 *
 */
public class PrintDictionary {
    // Outer Map maps Index in ProofString to Styling Info Map
    // Inner Map holds Styling Info separated for every Styling Case.
    // It's Keys are defined in the HighlightType enumeration
    // List: List of all Tags
    private Map<Integer, Map<Integer, List<String>>> openMap = new HashMap<>();
    private Map<Integer, Map<Integer, List<String>>> closeMap = new HashMap<>();

    private Map<HighlightType, List<Integer>> indicesListMap = new HashMap<>();

    /**
     * 
     */
    public PrintDictionary() {
        // TODO Auto-generated constructor stub
    }

    /**
     * inserts the tag into the given HashMap. Use only if you are sure you know
     * what to do
     * 
     * @param index
     *            position inside the proofstring
     * @param type
     *            the {@link HighlightType}
     * @param tag
     *            the tag itself.
     * @param map
     *            the map to be inserted into
     */
    private void putTag(int index, HighlightType type, String tag,
            Map<Integer, Map<Integer, List<String>>> map) {

        if (map.get(index) == null) {
            // If the Map Entry does not exist, create new Entry and call itself
            // again.
            map.put(index, new HashMap<Integer, List<String>>());
        }
        Map<Integer, List<String>> priorityMap = map.get(index);

        // ArrayList<String> tagList = mapValue[arrayPos.slotPosition];
        // If Array entry is null make ArrayList and add tag
        if (!priorityMap.containsKey(type.getPriority())) {
            priorityMap.put(type.getPriority(), new ArrayList<String>());
        }
        // If Tag is empty, one entry shall be removed
        if (tag.isEmpty() && priorityMap.get(type.getPriority()).size() > 0) {
            priorityMap.get(type.getPriority())
                    .remove(priorityMap.get(type.getPriority()).size() - 1);
        }
        else {
            // If the Array entry is not null, the tag can be appended.
            // Solves the problem with double consecutive chars
            // ("wellformed")
            priorityMap.get(type.getPriority()).add(tag);
            rememberIndices(index, type);
        }

    }

    /**
     * saves an opening tag (<span ...>) at the given position. Do not forget to
     * add a closing Tag!
     * 
     * @param index
     *            the inseriton position
     * @param type
     *            the {@link HighlightType}
     * @param tag
     *            the style tag constant
     */
    public void putOpenTag(int index, HighlightType type, String tag) {
        putTag(index, type, NUIConstants.OPEN_TAG_BEGIN.concat(tag)
                .concat(NUIConstants.OPEN_TAG_END), openMap);
    }

    /**
     * saves a closing tag (</span>) at the given position. Do not forget to add
     * an opening Tag!
     * 
     * @param index
     *            the inseriton position
     * @param type
     *            the {@link HighlightType}
     */
    public void putCloseTag(int index, HighlightType type) {
        putTag(index, type, NUIConstants.CLOSING_TAG, closeMap);
    }

    /**
     * saves the given indices in the indicesListMap for easier deletion
     * 
     * @param index
     *            the index to be saved
     * @param type
     *            the {@link HighlightType}
     */
    private void rememberIndices(int index, HighlightType type) {
        if (indicesListMap.get(type) == null) {
            indicesListMap.put(type, new ArrayList<>());
        }
        indicesListMap.get(type).add(index);
    }

    /**
     * removes all the opening tags at the given position for the
     * {@link HighlightType}. Do not forget to remove the closing tags!
     * 
     * @param index
     * @param type
     */
    public void removeOpenTag(int index, HighlightType type) {
        putTag(index, type, "", openMap);
    }

    /**
     * removes all the closing tags at the given position for the
     * {@link HighlightType}. Do not forget to remove the opening tags!
     * 
     * @param index
     * @param type
     */
    public void removeCloseTag(int index, HighlightType type) {
        putTag(index, type, "", closeMap);
    }

    /**
     * removes a Single Styling instance consisting of opening and closing tag
     * for a specific type
     * 
     * @param start
     * @param end
     * @param type
     */
    public void removeSingleStyleTag(int start, int end, HighlightType type) {
        putTag(start, type, "", openMap);
        putTag(end, type, "", closeMap);
    }

    /**
     * removes all the applied StyleTags for the given type
     * 
     * @param type
     */
    public void removeAllTypeTags(HighlightType type) {

        if (indicesListMap.get(type) == null) {
            return;
        }
        // Use Copy to avoid ConcurrentModificationException
        List<Integer> indicesList = new ArrayList<>(indicesListMap.get(type));
        for (Integer index : indicesList) {
            if (openMap.containsKey(index)) {
                removeOpenTag(index, type);
            }
            if (closeMap.containsKey(index)) {
                removeCloseTag(index, type);
            }
        }
        indicesListMap.get(type).clear();
    }

    /**
     * clears all the information
     */
    public void clear() {
        openMap.clear();
        closeMap.clear();
        indicesListMap.clear();
    }

    /**
     * @return a sorted List of Pairs, with the insertion index and the tag to
     *         be inserted. No offset has been computed.
     */
    // 2 separate LoopPhases for Tag Applying, to avoid self canceling and slim
    // down amount of tags.
    public List<Pair<Integer, String>> getTagList() {
        Set<Integer> keySet = new TreeSet<>();
        keySet.addAll(openMap.keySet());
        keySet.addAll(closeMap.keySet());
        List<Pair<Integer, String>> tagList = new ArrayList<>();

        Stack<Pair<Integer, String>> tagStack = new Stack<>();
        Stack<Pair<Integer, String>> saveTagStack = new Stack<>();

        List<String> insertTagList;

        for (Integer i : keySet) {
            // Apply Close Tags first
            if (closeMap.containsKey(i)) {
                for (int j = HighlightType.values().length - 1; j >= 0; j--) {
                    insertTagList = closeMap.get(i).get(j);
                    if (insertTagList == null)
                        continue;
                    for (String insertTag : insertTagList) {
                        if (insertTag == null || insertTag.isEmpty())
                            continue;

                        // Check for possible Overlap
                        while (!tagStack.isEmpty()
                                && tagStack.peek().first != j) {
                            tagList.add(new Pair<Integer, String>(i,
                                    NUIConstants.CLOSING_TAG));
                            saveTagStack.push(tagStack.pop());
                        }

                        tagList.add(new Pair<Integer, String>(i, insertTag));
                        tagStack.pop();

                        while (saveTagStack.size() > 0) {
                            tagList.add(new Pair<Integer, String>(i,
                                    saveTagStack.peek().second));
                            tagStack.push(saveTagStack.pop());
                        }
                    }
                }
            }
            // Apply OpenTags
            if (openMap.containsKey(i)) {
                for (int j = 0; j < HighlightType.values().length; j++) {
                    insertTagList = openMap.get(i).get(j);
                    if (insertTagList == null)
                        continue;
                    for (String insertTag : insertTagList) {
                        if (insertTag == null || insertTag.isEmpty())
                            continue;

                        // Correctly Prioritze even inside other spans
                        while (!tagStack.isEmpty()
                                && tagStack.peek().first > j) {
                            tagList.add(new Pair<Integer, String>(i,
                                    NUIConstants.CLOSING_TAG));
                            saveTagStack.push(tagStack.pop());
                        }

                        tagStack.push(new Pair<Integer, String>(j, insertTag));

                        tagList.add(new Pair<Integer, String>(i, insertTag));

                        while (saveTagStack.size() > 0) {
                            tagList.add(new Pair<Integer, String>(i,
                                    saveTagStack.peek().second));
                            tagStack.push(saveTagStack.pop());
                        }

                    }
                }
            }
        }
        return tagList;
    }
}
