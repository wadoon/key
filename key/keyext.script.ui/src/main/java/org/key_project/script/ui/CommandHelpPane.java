package org.key_project.script.ui;

import de.uka.ilkd.key.api.KeYApi;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import edu.kit.iti.formal.psdbg.interpreter.funchdl.CommandLookup;
import edu.kit.iti.formal.psdbg.interpreter.funchdl.DefaultLookup;
import edu.kit.iti.formal.psdbg.interpreter.funchdl.MacroCommandHandler;
import edu.kit.iti.formal.psdbg.interpreter.funchdl.ProofScriptCommandBuilder;
import edu.kit.iti.formal.psdbg.parser.ast.CallStatement;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.Setter;
import org.key_project.util.collection.ImmutableList;

import javax.swing.*;
import java.awt.*;
import java.util.ArrayList;
import java.util.List;

public class CommandHelpPane extends JPanel implements TabPanel {
    final MainWindow window;
    final KeYMediator mediator;

    private JEditorPane webView = new JEditorPane();

    private DefaultComboBoxModel<CommandEntry> model = new DefaultComboBoxModel<>();
    private JComboBox<CommandEntry> comboBox = new JComboBox<>(model);

    @Setter
    private CommandLookup commandLookup = new DefaultLookup();

    private Goal goal;

    private List<CommandEntry> fixedEntries = new ArrayList<>();

    public CommandHelpPane(MainWindow window, KeYMediator mediator) {
        this.window = window;
        this.mediator = mediator;
        //create default lookup, should later be replaced by the interpreter lookup
        DefaultLookup dl = new DefaultLookup();
        dl.getBuilders().add(new MacroCommandHandler(KeYApi.getMacroApi().getMacros()));
        dl.getBuilders().add(new ProofScriptCommandBuilder(KeYApi.getScriptCommandApi().getScriptCommands()));
        setCommandLookup(dl);

        KeYApi.getMacroApi().getMacros().forEach(proofMacro -> {
            fixedEntries.add(new CommandEntry(proofMacro.getScriptCommandName(), "macro"));
        });

        KeYApi.getScriptCommandApi().getScriptCommands().forEach(proofMacro -> {
            fixedEntries.add(new CommandEntry(proofMacro.getName(), "command"));
        });

        comboBox.addActionListener(e -> this.openHelpFor(((CommandEntry) model.getSelectedItem()).name));
        fixedEntries.forEach(model::addElement);


        setLayout(new BorderLayout());
        Box vbox = new Box(BoxLayout.X_AXIS);
        JLabel label = new JLabel("commands:");
        label.setLabelFor(comboBox);
        vbox.add(label);
        vbox.add(comboBox);
        add(vbox, BorderLayout.NORTH);
        add(webView);
    }

    public void setGoal(Goal g) {
        List<CommandEntry> l = new ArrayList<>(fixedEntries);
        ProofControl c = mediator.getUI().getProofControl();
        ImmutableList<TacletApp> a = c.getNoFindTaclet(g);
        a.forEach(app ->
                l.add(new CommandEntry(app.taclet().name().toString(), "taclet, no pos"))
        );

        /*
            final ImmutableList<BuiltInRule> builtInRules = c.getBuiltInRule(goal, occ);
            removeRewrites(c.getFindTaclet(goal, occ))
                            .prepend(c.getRewriteTaclet(goal, occ)),
                    c.getNoFindTaclet(goal), builtInRules);
            */
        // Is there a better for finding all taclets?????
        model.removeAllElements();
        l.forEach(model::addElement);
    }

    private void openHelpFor(String name) {
        CallStatement cs = new CallStatement();
        cs.setCommand(name);
        String html = commandLookup.getHelp(cs);
        webView.setText(html);
        webView.setContentType("text/html");
    }

    @Override
    public Icon getIcon() {
        return IconFontSwing.buildIcon(FontAwesomeSolid.QUESTION_CIRCLE, 16);
    }

    @Override
    public String getTitle() {
        return "Command Help";
    }

    @Override
    public JComponent getComponent() {
        return this;
    }

    @Data
    @AllArgsConstructor
    class CommandEntry {
        String name, additionalInformation;


        @Override
        public String toString() {
            return beautifyName(name) + " (" + additionalInformation + ")";
        }

        private String beautifyName(String cname) {
            String ret;
            if (cname.contains("-")) {
                ret = cname.replace("-", "_");
                return ret;
            } else {
                return cname;
            }
        }
    }
}
