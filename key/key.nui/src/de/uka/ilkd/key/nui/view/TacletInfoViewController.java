package de.uka.ilkd.key.nui.view;

import java.net.URL;
import java.util.ResourceBundle;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.core.KeYMediator;
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
import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.nui.model.IProofListener;
import de.uka.ilkd.key.pp.IdentitySequentPrintFilter;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.pp.SequentPrintFilter;
import de.uka.ilkd.key.pp.SequentViewLogicPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.NewDependingOn;
import de.uka.ilkd.key.rule.NewVarcond;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.GenericSortInstantiations;
import javafx.application.Platform;
import javafx.fxml.FXML;
import javafx.scene.control.TextArea;

@KeYView(title = "TacletInfo", path = "TacletInfoView.fxml", preferredPosition = ViewPosition.TOPRIGHT, hasMenuItem = false)
public class TacletInfoViewController extends ViewController {


    private KeYMediator mediator;
    private Node node;
    private IdentitySequentPrintFilter filter;
    @FXML
    private TextArea outputText;
    
    private IProofListener proofChangeListener = (proofEvent) -> {
        // execute ui update on javafx thread
        Platform.runLater(() -> {
            mediator = getContext().getProofManager().getMediator();
            showTacletInfo();
        });
    };
    
    @Override
    public void initialize(URL arg0, ResourceBundle arg1) {
        // TODO Auto-generated method stub
    }
    
    @Override
    public void initializeAfterLoadingFxml() {
        getContext().getProofManager().addProofListener(proofChangeListener);
    }
    
    private void showTacletInfo(){
        node = mediator.getSelectedNode();
        filter = new IdentitySequentPrintFilter(node.sequent());
        outputText.setText(getTacletDescription(mediator, node, filter));
    };
    
    
    private String getTacletDescription(KeYMediator mediator,
            Node node,
            SequentPrintFilter filter) {

        RuleApp app = node.getAppliedRuleApp();
        StringBuilder s = new StringBuilder();

        if (app != null) {
            s.append("The following rule was applied on this node: \n\n");
            if (app.rule() instanceof Taclet) {
                LogicPrinter logicPrinter = new LogicPrinter(new ProgramPrinter(null),
                        mediator.getNotationInfo(),
                        mediator.getServices(),
                        true);
                logicPrinter.printTaclet((Taclet) (app.rule()));
                s.append(logicPrinter);
            } else {
                s.append(app.rule());
            }

            if (app instanceof TacletApp) {
                TacletApp tapp = (TacletApp) app;
                if (tapp.instantiations().getGenericSortInstantiations()
                        != GenericSortInstantiations.EMPTY_INSTANTIATIONS) {
                    s.append("\n\nWith sorts:\n");
                    s.append(tapp.instantiations().getGenericSortInstantiations());
                }

                StringBuffer sb = new StringBuffer("\n\n");
                //TODO 
                writeTacletSchemaVariablesHelper(sb, tapp.taclet());
                s.append(sb);
            }
        } else {
            s.append("No rule was applied on this node.");
        }
        return s.toString();
    }
    
    private static void writeTacletSchemaVariablesHelper(StringBuffer out,
            final Taclet t) {
        ImmutableSet<SchemaVariable> schemaVars = t.getIfFindVariables();

        for (final NewVarcond nvc: t.varsNew()) {
            schemaVars = schemaVars.add(nvc.getSchemaVariable());
        }

        for (final NewDependingOn ndo : t.varsNewDependingOn()) {
            schemaVars = schemaVars.add(ndo.first());
        }

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
    
    private static void writeTacletSchemaVariable(StringBuffer out,
            SchemaVariable schemaVar) {
        if (schemaVar instanceof ModalOperatorSV) {
            final ModalOperatorSV modalOpSV = (ModalOperatorSV) schemaVar;
            String sep = "";
            for (final Operator op : modalOpSV.getModalities()) {
                out.append(sep);
                out.append(op.name());
                sep = ", ";
            }
            out.append(" } ").append(modalOpSV.name());
        } else if (schemaVar instanceof TermSV) {
            out.append("\\term");
        } else if (schemaVar instanceof FormulaSV) {
            out.append("\\formula");
        } else if (schemaVar instanceof UpdateSV) {
            out.append("\\update");
        } else if (schemaVar instanceof ProgramSV) {
            out.append("\\program");
        } else if (schemaVar instanceof VariableSV) {
            out.append("\\variables");
        } else if (schemaVar instanceof SkolemTermSV) {
            out.append("\\skolemTerm");
        } else if (schemaVar instanceof TermLabelSV) {
            out.append("\\termlabel");
        } else {
            out.append("?");
        }
        writeSVModifiers(out, schemaVar);

        /*
         * TODO: Add an explanation for the following if-statement.
         * (Kai Wallisch 01/2015)
         */
        if (!(schemaVar instanceof FormulaSV
                || schemaVar instanceof UpdateSV
                || schemaVar instanceof TermLabelSV)) {
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
            } else {
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
