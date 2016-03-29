package de.uka.ilkd.key.nui.printer;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.nodeviews.InnerNodeView;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SkolemTermSV;
import de.uka.ilkd.key.logic.op.TermLabelSV;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.NewVarcond;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.GenericSortInstantiations;

/**
 * Printer class for generating Strings containing information about applied
 * rules. Methods copied from {@link InnerNodeView} with minor adaptions.
 * 
 * @author Victor Schuemmer
 * @version 1.0
 */
public class TacletInfoPrinter {

    /**
     * Creates a String containing information about applied rules on the given
     * node.
     * 
     * @param mediator
     *            {@link KeYMediator}
     * @param node
     *            {@link Node}
     * @return String containing information about applied rules on the given
     *         node.
     */
    public static String printTacletInfo(KeYMediator mediator, Node node) {

        RuleApp app = node.getAppliedRuleApp();
        StringBuilder s = new StringBuilder();

        if (app != null) {
            s.append("The following rule was applied on this node: \n\n");
            if (app.rule() instanceof Taclet) {
                LogicPrinter logicPrinter = new LogicPrinter(new ProgramPrinter(null), mediator.getNotationInfo(),
                        mediator.getServices(), true);
                logicPrinter.printTaclet((Taclet) (app.rule()));
                s.append(logicPrinter);
            }
            else {
                s.append(app.rule());
            }

            if (app instanceof TacletApp) {
                TacletApp tapp = (TacletApp) app;
                if (tapp.instantiations()
                        .getGenericSortInstantiations() != GenericSortInstantiations.EMPTY_INSTANTIATIONS) {
                    s.append("\n\nWith sorts:\n");
                    s.append(tapp.instantiations().getGenericSortInstantiations());
                }

                StringBuffer sb = new StringBuffer("\n\n");
                writeTacletSchemaVariablesHelper(sb, tapp.taclet());
                s.append(sb);
            }
        }
        else {
            s.append("No rule was applied on this node.");
        }
        return s.toString();
    }

    private static void writeTacletSchemaVariablesHelper(StringBuffer out, final Taclet t) {
        ImmutableSet<SchemaVariable> schemaVars = t.getIfFindVariables();

        for (final NewVarcond nvc : t.varsNew()) {
            schemaVars = schemaVars.add(nvc.getSchemaVariable());
        }

        // for (final NewDependingOn ndo : t.varsNewDependingOn()) {
        // schemaVars = schemaVars.add(ndo.first());
        // }

        if (!schemaVars.isEmpty()) {
            out.append("\\schemaVariables {\n");
            for (SchemaVariable schemaVar1 : schemaVars) {
                final SchemaVariable schemaVar = schemaVar1;
                // write indentation
                out.append("  ");
                // write declaration
                writeTacletSchemaVariable(out, schemaVar);
                // write newline
                out.append(";\n");
            }
            out.append("}\n");
        }
    }

    private static void writeTacletSchemaVariable(StringBuffer out, SchemaVariable schemaVar) {
        if (schemaVar instanceof ModalOperatorSV) {
            final ModalOperatorSV modalOpSV = (ModalOperatorSV) schemaVar;
            String sep = "";
            for (final Operator op : modalOpSV.getModalities()) {
                out.append(sep);
                out.append(op.name());
                sep = ", ";
            }
            out.append(" } ").append(modalOpSV.name());
        }
        else if (schemaVar instanceof TermSV) {
            out.append("\\term");
        }
        else if (schemaVar instanceof FormulaSV) {
            out.append("\\formula");
        }
        else if (schemaVar instanceof UpdateSV) {
            out.append("\\update");
        }
        else if (schemaVar instanceof ProgramSV) {
            out.append("\\program");
        }
        else if (schemaVar instanceof VariableSV) {
            out.append("\\variables");
        }
        else if (schemaVar instanceof SkolemTermSV) {
            out.append("\\skolemTerm");
        }
        else if (schemaVar instanceof TermLabelSV) {
            out.append("\\termlabel");
        }
        else {
            out.append("?");
        }
        writeSVModifiers(out, schemaVar);

        /*
         * TODO: Add an explanation for the following if-statement. (Kai
         * Wallisch 01/2015)
         */
        if (!(schemaVar instanceof FormulaSV || schemaVar instanceof UpdateSV || schemaVar instanceof TermLabelSV)) {
            out.append(" ").append(schemaVar.sort().declarationString());
        }
        out.append(" ").append(schemaVar.name());
    }

    private static void writeSVModifiers(StringBuffer out, SchemaVariable sv) {
        boolean started = false;
        if (sv.isRigid() && !(sv instanceof VariableSV)) {
            if (!started) {
                out.append("[");
            }
            out.append("rigid");
            started = true;
        }
        if (sv instanceof ProgramSV && ((ProgramSV) sv).isListSV()) {
            if (!started) {
                out.append("[");
            }
            else {
                out.append(", ");
            }
            out.append("list");
            started = true;
        }

        if (started) {
            out.append("]");
        }
    }
}
