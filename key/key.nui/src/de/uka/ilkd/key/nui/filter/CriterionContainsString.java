package de.uka.ilkd.key.nui.filter;

import java.util.LinkedList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * A criteria that meets any line that contains the search text.
 * 
 * @author Benedikt Gross
 */
public class CriterionContainsString implements Criterion<Integer> {

    private String searchText;
    private String[] originalLines;
    private String proofString;

    public CriterionContainsString(String searchText, String[] originalLines,
            String proofString) {
        if (searchText == null)
            throw new IllegalArgumentException("searchText");
        this.searchText = searchText;
        if (originalLines != null) {
            this.originalLines = (String[]) originalLines.clone();
        }
        this.proofString = proofString;
    }

    @Override
    public List<Integer> meetCriteria(List<Integer> lines) {
        /*
         * List<Integer> list = new LinkedList<>(); for (Integer lineIndex :
         * lines) { if (originalLines[lineIndex] != null &&
         * originalLines[lineIndex].contains(searchText)) { list.add(lineIndex);
         * } } return list;
         */
        List<Integer> list = new LinkedList<>();
        Pattern p = Pattern.compile(Pattern.quote(searchText));
        Matcher matcher = p.matcher(proofString);
        while (matcher.find()) {
            // add multiple lines if match was across multiples lines
            int startLine = LineToPrintedProofPosition
                    .getLineIndex(matcher.start(), originalLines);
            int endLine = LineToPrintedProofPosition.getLineIndex(matcher.end(),
                    originalLines);
            list.addAll(IntStream.range(startLine, endLine + 1).distinct()
                    .boxed().collect(Collectors.toList()));
        }

        // remove matches that where not in the already filtered lines
        for (int i = list.size() - 1; i >= 0; i--) {
            if (!lines.contains(list.get(i)))
                list.remove(i);
        }

        return list.stream().distinct().collect(Collectors.toList());
    }
}
