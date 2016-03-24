package de.uka.ilkd.key.nui.printer;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.nui.util.NUIConstants;
import de.uka.ilkd.key.util.Pair;

/**
 * Holds all the Highlighting Information used by the {@link SequentPrinter}.
 * 
 * @author Maximilian Li
 * @version 1.0
 */
public class PrintDictionary {
    // Outer Map maps Index in ProofString to Styling Info Map.
    // Inner Map holds Styling Info separated for every Styling Case.
    // Its Keys are defined in the HighlightType enumeration.
    // List: List of all Tags
    private Map<Integer, Map<Integer, List<String>>> openMap = new HashMap<>();
    private Map<Integer, Map<Integer, List<String>>> closeMap = new HashMap<>();

    // An additional Map holding the Indices to simplify deletion
    private Map<HighlightType, List<Integer>> indicesListMap = new HashMap<>();

    /**
     * Inserts the tag into the given {@link HashMap}. Use only if you are sure
     * you know what to do.
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
     * Puts an opening tag at the start position and a closing one at the end
     * position. Checks if start <= end.
     * 
     * @param start
     *            start position inside the proof string
     * @param end
     *            end position inside the proof string
     * @param type
     *            the {@link HighlightType}
     * @param tag
     *            the opening tag constant
     * @return a boolean indicating if the insertion was successful
     */
    protected boolean putStyleTags(int start, int end, HighlightType type,
            String tag) {
        if (start >= end) {
            return false;
        }
        putOpenTag(start, type, tag);
        putCloseTag(end, type);
        return true;
    }

    /**
     * Saves an opening tag (<span ...>) at the given position. Do not forget to
     * add a closing tag!
     * 
     * @param index
     *            the insertion position
     * @param type
     *            the {@link HighlightType}
     * @param tag
     *            the style tag constant
     */
    protected void putOpenTag(int index, HighlightType type, String tag) {
        putTag(index, type, NUIConstants.OPEN_TAG_BEGIN.concat(tag)
                .concat(NUIConstants.OPEN_TAG_END), openMap);
    }

    /**
     * Saves a closing tag (</span>) at the given position. Do not forget to add
     * an opening tag!
     * 
     * @param index
     *            the insertion position
     * @param type
     *            the {@link HighlightType}
     */
    protected void putCloseTag(int index, HighlightType type) {
        putTag(index, type, NUIConstants.CLOSING_TAG, closeMap);
    }

    /**
     * Saves the given indices in the {@link #indicesListMap} for easier
     * deletion.
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
     * Removes all the opening tags at the given position for the
     * {@link HighlightType}. Do not forget to remove the closing tags!
     * 
     * @param index
     *            index to be removed
     * @param type
     *            {@link HighlightType}
     */
    public void removeOpenTag(int index, HighlightType type) {
        putTag(index, type, "", openMap);
    }

    /**
     * Removes all the closing tags at the given position for the
     * {@link HighlightType}. Do not forget to remove the opening tags!
     * 
     * @param index
     *            index to be removed
     * @param type
     *            {@link HighlightType}
     */
    public void removeCloseTag(int index, HighlightType type) {
        putTag(index, type, "", closeMap);
    }

    /**
     * Removes a Single Styling instance consisting of opening and closing tag
     * for a specific type.
     * 
     * @param start
     *            start index
     * @param end
     *            end index
     * @param type
     *            {@link HighlightType}
     */
    public void removeSingleStyleTag(int start, int end, HighlightType type) {
        putTag(start, type, "", openMap);
        putTag(end, type, "", closeMap);
    }

    /**
     * Removes all the applied StyleTags for the given type.
     * 
     * @param type
     *            {@link HighlightType}
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
     * Clears all the information.
     */
    public void clear() {
        openMap.clear();
        closeMap.clear();
        indicesListMap.clear();
    }

    /**
     * @return A sorted List of Pairs, with the insertion index and the tag to
     *         be inserted. No offset has been computed.
     */
    public List<Pair<Integer, String>> getTagList() {
        DictionaryFlattener flattener = new DictionaryFlattener();
        return flattener.flatten(openMap, closeMap);
    }
}
