package edu.kit.iti.formal.psdbg.storage;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import javafx.util.Pair;
import lombok.val;

import java.util.*;
import java.util.function.Function;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (16.05.18)
 */
public class WalkableLabelFacade {
    public static final String SUFFIX_COMPRESSED_LABEL = "}";
    public static final String PREFIX_COMPRESSED_LABEL = "{";
    public static final String SUFFIX_WALKABLE_LABEL = "]";
    public static final String PREFIX_WALKABLE_LABEL = "[";
    public static final String ENTRY_DELIMITER = ",";
    public static final String LENGTH_DELIMITER = "|";


    public static String getCompressedWalkableLabel(Node node) {
        ArrayList<Integer> walk = getWalkForNode(node);
        Collection<Pair<Integer, Integer>> cwalk = compress(walk.iterator());
        return cwalk.stream()
                .map(p -> p.getKey() + LENGTH_DELIMITER + p.getValue())
                .collect(Collectors.joining(ENTRY_DELIMITER, PREFIX_COMPRESSED_LABEL, SUFFIX_COMPRESSED_LABEL));
    }

    public static String getWalkableLabel(Node node) {
        val walk = getWalkForNode(node);
        return walk.stream()
                .map(Object::toString)
                .collect(Collectors.joining(ENTRY_DELIMITER, PREFIX_WALKABLE_LABEL, SUFFIX_WALKABLE_LABEL));
    }

    static ArrayList<Integer> getWalkForNode(Node current) {
        if (current == null) throw new IllegalArgumentException();
        ArrayList<Integer> walk = new ArrayList<>(1024 * 16);

        while (current != null) {
            Node parent = current.parent();
            if (parent == null) break;
            walk.add(parent.getChildNr(current));
            current = parent;
        }
        Collections.reverse(walk);
        return walk;
    }

    static <T> Collection<T> parseUncompressed(String input, String prefix, String suffix,
                                               String delimEntries, Function<String, T> parse) {
        input = removePrefixAndSuffix(input, prefix, suffix);
        Pattern reOuter = Pattern.compile(delimEntries);
        Collection<T> seq = new ArrayList<>();
        reOuter.splitAsStream(input).forEach(
                chunk -> {
                    T obj = parse.apply(chunk);
                    seq.add(obj);
                }
        );
        return seq;
    }

    private static String removePrefixAndSuffix(String input, String prefix, String suffix) {
        if (input.startsWith(prefix))
            input = input.substring(prefix.length());

        if (input.endsWith(suffix))
            input = input.substring(0, input.length() - suffix.length());
        return input;
    }

    static <T> Collection<Pair<Integer, T>> parseCompressed(String input, String prefix, String suffix,
                                                            String delimEntries, String delimLength,
                                                            Function<String, T> parse) {
        input = removePrefixAndSuffix(input, prefix, suffix);

        Pattern reOuter = Pattern.compile(delimEntries);
        Collection<Pair<Integer, T>> seq = new ArrayList<>();
        reOuter.splitAsStream(input).forEach(
                chunk -> {
                    String s[] = chunk.split(Pattern.quote(delimLength));
                    int length = Integer.parseInt(s[0]);
                    T obj = parse.apply(s[1]);
                    seq.add(new Pair<>(length, obj));
                }
        );
        return seq;
    }

    /**
     * Uncompress a given run-length encoding.
     *
     * @param iter
     * @param <T>  an arbitrary type
     * @return
     */
    static <T> Collection<T> uncompress(Iterator<Pair<Integer, T>> iter) {
        List<T> seq = new ArrayList<>();
        while (iter.hasNext()) {
            Pair<Integer, T> p = iter.next();
            int length = p.getKey();
            T obj = p.getValue();
            for (int i = 0; i < length; i++)
                seq.add(obj);
        }
        return seq;
    }

    /**
     * run length compression
     *
     * @param iter
     * @param <T>
     * @return
     */
    static <T> Collection<Pair<Integer, T>> compress(Iterator<T> iter) {
        if (iter.hasNext()) {
            List<Pair<Integer, T>> compress = new ArrayList<>();
            T last = iter.next();
            int length = 1;

            while (iter.hasNext()) {
                T n = iter.next();
                if (n.equals(last)) {
                    length++;
                } else {
                    compress.add(new Pair<>(length, last));
                    last = n;
                    length = 1;
                }
            }
            compress.add(new Pair<>(length, last));
            return compress;
        } else {
            return Collections.emptyList();
        }
    }


    public static Node findNode(Proof proof, String identifier) {
        if (identifier.startsWith(PREFIX_WALKABLE_LABEL)
                && identifier.endsWith(SUFFIX_WALKABLE_LABEL)) {
            Collection<Integer> seq =
                    parseUncompressed(identifier, PREFIX_WALKABLE_LABEL, SUFFIX_WALKABLE_LABEL,
                            ENTRY_DELIMITER, Integer::parseInt);
            return findNode(proof, seq);
        }

        if (identifier.startsWith(PREFIX_COMPRESSED_LABEL)
                && identifier.endsWith(SUFFIX_COMPRESSED_LABEL)) {
            Collection<Pair<Integer, Integer>> seq = parseCompressed(identifier, PREFIX_COMPRESSED_LABEL, SUFFIX_COMPRESSED_LABEL,
                    ENTRY_DELIMITER, LENGTH_DELIMITER, Integer::parseInt);
            return findNode(proof, uncompress(seq.iterator()));
        }

        throw new IllegalArgumentException("Given identifier is a valid walkable label");
    }

    public static Node findNode(Proof proof, Collection<Integer> walk) {
        Node current = proof.root();
        for (Integer i : walk) {
            current = current.child(i);
        }
        return current;
    }
}
