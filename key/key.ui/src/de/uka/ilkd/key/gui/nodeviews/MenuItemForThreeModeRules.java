package de.uka.ilkd.key.gui.nodeviews;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;

import javax.swing.JMenu;
import javax.swing.JMenuItem;

import de.uka.ilkd.key.rule.BuiltInRule;

/**
 * This class was copy pasted from MenuItemForTwoModeRules (with some minor modifications)
 * TODO: extract common interface for MenuItemForTwoModeRules and MenuItemForThreeModeRules
 *
 * @author Jakob Laenge
 */
public class MenuItemForThreeModeRules extends JMenu implements BuiltInRuleMenuItem {

	private static final int EXPAND_DELAY = 200;
	private static final long serialVersionUID = 2002938010823537470L;

	// without selecting one the options above take unforced mode as default
	private enum Mode {
		FORCED, ABSTRACT, INTERACTIVE
	}
	private static final Mode DEFAULT_MODE = Mode.FORCED;

	private final BuiltInRule rule;
	private Mode mode = DEFAULT_MODE;
	// we support only one listener
	private ActionListener listener;

	public MenuItemForThreeModeRules(String mainName, 
            String actionTextForForcedMode, String tooltipForcedMode,
            String actionTextForAbstractMode, String tooltipAbstractMode,
            String actionTextForInteractiveMode, String tooltipInteractiveMode, 
            BuiltInRule rule) {
        super(mainName);
        this.rule = rule;    
        init(actionTextForForcedMode, tooltipForcedMode,
        	actionTextForAbstractMode, tooltipAbstractMode,
            actionTextForInteractiveMode, tooltipInteractiveMode);    
    }

	private void init(String actionTextForForcedMode, String tooltipForcedMode,
			String actionTextForAbstractMode, String tooltipAbstractMode,
			String actionTextForInteractiveMode, String tooltipInteractiveMode) {
		// forced mode
		JMenuItem forcedModeItem = new JMenuItem(actionTextForForcedMode);
		forcedModeItem.setToolTipText(tooltipForcedMode);
		add(forcedModeItem);
		forcedModeItem.addActionListener(new ActionListener() {
			@Override
			public void actionPerformed(ActionEvent e) {
				mode = Mode.FORCED;
				listener.actionPerformed(new ActionEvent(MenuItemForThreeModeRules.this, ActionEvent.ACTION_PERFORMED,
						e.getActionCommand()));
			}
		});
		// abstract mode
		JMenuItem abstractModeItem = new JMenuItem(actionTextForAbstractMode);
		abstractModeItem.setToolTipText(tooltipAbstractMode);
		add(abstractModeItem);
		abstractModeItem.addActionListener(new ActionListener() {
			@Override
			public void actionPerformed(ActionEvent e) {
				mode = Mode.ABSTRACT;
				listener.actionPerformed(new ActionEvent(MenuItemForThreeModeRules.this, ActionEvent.ACTION_PERFORMED,
						e.getActionCommand()));
			}
		});
		// interactive mode
		JMenuItem interactiveModeItem = new JMenuItem(actionTextForInteractiveMode);
		interactiveModeItem.setToolTipText(tooltipInteractiveMode);
		add(interactiveModeItem);
		interactiveModeItem.addActionListener(new ActionListener() {
			@Override
			public void actionPerformed(ActionEvent e) {
				mode = Mode.INTERACTIVE;
				listener.actionPerformed(new ActionEvent(MenuItemForThreeModeRules.this, ActionEvent.ACTION_PERFORMED,
						e.getActionCommand()));
			}
		});

		// without selecting one the options above take forced mode as default
		super.addActionListener(new ActionListener() {
			@Override
			public void actionPerformed(ActionEvent e) {
				mode = DEFAULT_MODE;
				listener.actionPerformed(new ActionEvent(MenuItemForThreeModeRules.this, ActionEvent.ACTION_PERFORMED,
						e.getActionCommand()));
			}
		});

		// wait a bit longer before expanding submenus
		setDelay(getDelay() + EXPAND_DELAY);

		super.addMouseListener(new MouseAdapter() {
			@Override
			public void mouseClicked(MouseEvent e) {
				mode = DEFAULT_MODE;

				listener.actionPerformed(
						new ActionEvent(MenuItemForThreeModeRules.this, ActionEvent.ACTION_PERFORMED, getText()));
				MenuItemForThreeModeRules.this.getParent().setVisible(false);
			}
		});

	}

	@Override
	public void addActionListener(ActionListener listener) {
		this.listener = listener;
	}

	@Override
	public void removeActionListener(ActionListener listener) {
		if (this.listener == listener) {
			this.listener = null;
		}
	}

	@Override
	public BuiltInRule connectedTo() {
		return rule;
	}

	@Override
	public boolean forcedApplication() {
		return (mode == Mode.FORCED);
	}

}
