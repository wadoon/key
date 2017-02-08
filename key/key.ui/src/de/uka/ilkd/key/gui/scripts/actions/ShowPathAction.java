package de.uka.ilkd.key.gui.scripts.actions;

import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.prooftree.PathFilter;
import de.uka.ilkd.key.gui.scripts.ActualScript;
import de.uka.ilkd.key.gui.scripts.ScriptView;
import de.uka.ilkd.key.macros.scripts.ScriptNode;
import de.uka.ilkd.key.proof.Node;

import java.awt.event.ActionEvent;
import java.util.List;

/**
 * Created by sarah on 2/6/17.
 */
public class ShowPathAction extends AbstractScriptAction {

    private ScriptView view;
    private ActualScript script;
    public final static String name = "Show Path";

    public ShowPathAction(ScriptView view, ActualScript script){
        super(name, view, script);
        this.view = view;
        this.script = script;


    }

    @Override
    public void actionPerformed(ActionEvent actionEvent) {
         int pos = view.getTextArea().getCaretPosition();
          view.getTextArea().setCaretPosition(pos);
          showPath(pos);
    }

    private void showPath(int pos){
        if(script.getCurrentRoot() == null)
            ExceptionDialog.showDialog(view.getMainWindow(), new Exception("There is currently no parsed script tree to browse."));
        ScriptNode snode = view.getNodeAtPos(script.getCurrentRoot(), pos);
        if(snode != null) {
            Node proofNode = snode.getProofNode();
            if(proofNode != null) {
                List<Node> nodes = script.getPaths(proofNode);
                //Filter Nodes acc. to nodes List
                PathFilter pf = new PathFilter(nodes);
                view.getMainWindow().getProofTreeView().setFilter(pf);
            }
        }
    }
}
