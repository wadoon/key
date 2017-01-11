package de.uka.ilkd.key.gui;

import java.awt.BorderLayout;
import java.awt.Font;
import java.awt.Point;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.io.IOException;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.ServiceLoader;

import javax.swing.JButton;
import javax.swing.JMenuItem;
import javax.swing.JPanel;
import javax.swing.JPopupMenu;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.JToolBar;
import javax.swing.SwingUtilities;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.macros.scripts.AbstractCommand;
import de.uka.ilkd.key.macros.scripts.ProofScriptCommand;
import de.uka.ilkd.key.macros.scripts.ScriptException;
import de.uka.ilkd.key.macros.scripts.ScriptNode;
import de.uka.ilkd.key.macros.scripts.ScriptTreeParser;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

@SuppressWarnings("serial")
public class ScriptView extends JPanel{

//    private static final Map<String, ProofScriptCommand> COMMANDS = loadCommands();

//    private static final Map<String, String> SKIP = Collections.singletonMap("#1", "skip");

    private JTextArea textArea;
    //private KeYMediator mediator;
    private MainWindow mainWindow;
    private JButton b;

    public JTextArea getTextArea() {
        return textArea;
    }

    public JButton getB() {
        return b;
    }

    public JButton getP() {
        return p;
    }

    public JButton getG() {
        return g;
    }

    private JButton p;
    private JButton g;


    public ScriptView(KeYMediator mediator, MainWindow mainWindow) {
        this.mainWindow = mainWindow;
        init();
    }

    private void init() {
        setLayout(new BorderLayout());
        {
            JToolBar bar = new JToolBar();
            bar.setFloatable(false);
            {
                b = new JButton("R");
                b.setActionCommand("reset");
                bar.add(b);
            }
            {
                p = new JButton("P");
                p.setActionCommand("parse");
                bar.add(p);
            }
            {
                g = new JButton("G");
                g.setActionCommand("goto");
                bar.add(g);
            }
            add(bar, BorderLayout.NORTH);
        }
        {
            textArea = new JTextArea();
            textArea.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 12));
            add(new JScrollPane(textArea), BorderLayout.CENTER);

        }
    }





}
