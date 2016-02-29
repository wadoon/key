package de.uka.ilkd.key.nui.filter;

import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.uka.ilkd.key.pp.InitialPositionTable;

public class SequentFilterer {

    /**
     * Applies a criteria to the proofString and returns all lines, that should
     * be displayed to the user after filtering.
     */
    public static List<Integer> applyFilter(String proofString,
            PrintFilter filter, InitialPositionTable positionTable) {
        String[] lines = proofString.split("\n");
        return compileCriteria(filter, positionTable, lines)
                // pass list with all indices
                .meetCriteria(IntStream.range(0, lines.length).boxed()
                        .collect(Collectors.toList()));
    }

    /**
     * Creates a criteria for filtering the sequent from all information that is
     * stored in this object.
     */
    private static Criterion<Integer> compileCriteria(PrintFilter filter,
            InitialPositionTable positionTable, String[] originalLines) {

        Criterion<Integer> criteria;

        if (filter == null) {
            criteria = new CriterionEmpty<>();
            return criteria;
        }

        if (filter.getIsUserCriteria()) {
            if (filter.getSearchText() == null)
                criteria = new CriterionEmpty<>();
            else
                criteria = new CriterionContainsString(filter.getSearchText(),
                        originalLines);
        }
        else {
            if (filter.getSelections().size() == 0)
                criteria = new CriterionEmpty<>();
            else
                criteria = compileSelectionCriteria(filter.getSelections(),
                        originalLines);
        }

        // X: it may be better to apply this after invert, depends on user
        // experience
        if (!filter.getUseAstScope())
            if (filter.getBefore() != 0 || filter.getAfter() != 0) {
                criteria = new CriterionRange(criteria, filter.getBefore(),
                        filter.getAfter(), originalLines);
            }

        // apply invert as last
        if (filter.getInvert())
            criteria = new NotCriterion<>(criteria);

        if (filter.getUseAstScope())
            criteria = new CriterionAstScope(criteria, positionTable,
                    originalLines);

        return criteria;
    }

    private static Criterion<Integer> compileSelectionCriteria(
            List<String> selections, String[] originalLines) {
        Criterion<Integer> criteria;
        if (selections == null || selections.size() == 0) {
            criteria = new CriterionEmpty<Integer>();
            return criteria;
        }

        criteria = new CriterionContainsString(selections.get(0),
                originalLines);
        for (int i = 1; i < selections.size(); i++) {
            criteria = new OrCriterion<>(new CriterionContainsString(
                    selections.get(i), originalLines), criteria);
        }

        return criteria;
    }
}
