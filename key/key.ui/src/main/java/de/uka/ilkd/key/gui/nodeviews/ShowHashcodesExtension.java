package de.uka.ilkd.key.gui.nodeviews;

import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.util.AbstractExecutionUtils;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.pp.PosInSequent;

/**
 * Extension adapter for showing hash codes for terms. Useful for debugging.
 *
 * @author Dominic Steinhoefel
 */
@KeYGuiExtension.Info( //
        name = "Show Hashcodes", //
        optional = true, //
        description = "GUI Extension for showing hash codes in tooltips", //
        experimental = false)
public class ShowHashcodesExtension implements KeYGuiExtension, KeYGuiExtension.Tooltip {

    @Override
    public List<String> getTooltipStrings(MainWindow mainWindow, PosInSequent pos) {
        if (pos == null || pos.isSequent()) {
            return Collections.emptyList();
        }

        String result = "";

        final Term term = pos.getPosInOccurrence().subTerm();
        result += "<b>Operator Hash:</b> " + term.op().hashCode();

        if (term.op() instanceof ElementaryUpdate) {
            result += "<br><b>LHS Hash:</b> " + ((ElementaryUpdate) term.op()).lhs().hashCode();
            result += "<br><b>LHS Sort:</b> "
                    + ((ElementaryUpdate) term.op()).lhs().sort().toString();
        }

        if (term.op() instanceof AbstractUpdate) {
            result += "<br><b>LHS Hashes:</b> " + ((AbstractUpdate) term.op()).getAllAssignables()
                    .stream().map(AbstractExecutionUtils::unwrapHasTo).map(Object::hashCode)
                    .map(i -> "" + i).collect(Collectors.joining(", "));
            result += "<br><b>LHS Sorts:</b> " + ((AbstractUpdate) term.op()).getAllAssignables()
                    .stream().map(AbstractExecutionUtils::unwrapHasTo).map(AbstractUpdateLoc::sort)
                    .map(i -> "" + i).collect(Collectors.joining(", "));
        }

        return Collections.singletonList(result);
    }
}
