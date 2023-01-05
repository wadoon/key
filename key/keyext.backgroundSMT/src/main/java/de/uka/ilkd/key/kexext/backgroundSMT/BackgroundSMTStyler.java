package de.uka.ilkd.key.kexext.backgroundSMT;

import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.fonticons.IconFont;
import de.uka.ilkd.key.gui.fonticons.IconFontProvider;
import de.uka.ilkd.key.gui.prooftree.GUIAbstractTreeNode;
import de.uka.ilkd.key.gui.prooftree.Style;
import de.uka.ilkd.key.gui.prooftree.Styler;

import javax.annotation.Nonnull;
import javax.swing.*;
import java.awt.event.ActionEvent;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.util.Timer;
import java.util.TimerTask;

public class BackgroundSMTStyler implements Styler<GUIAbstractTreeNode> {
    private final BackgroundSMTExtension extension;

    public BackgroundSMTStyler(BackgroundSMTExtension extension) {
        this.extension = extension;
    }
    @Override
    public void style(@Nonnull Style current, @Nonnull GUIAbstractTreeNode obj) {

        JButton bsmt_button;

        if (extension.canApply(obj.getNode())) {
            bsmt_button = new JButton(new AbstractAction() {
                @Override
                public void actionPerformed(ActionEvent actionEvent) {
                    extension.applyRunner(obj.getNode());
                }
            });
            bsmt_button.setEnabled(true);
            bsmt_button.setIcon(IconFactory.get(new IconFontProvider(FontAwesomeSolid.FAST_FORWARD), 12));
        } else {
            bsmt_button = new JButton(IconFactory.get(new IconFontProvider(FontAwesomeSolid.FAST_BACKWARD), 12));
            bsmt_button.setEnabled(false);
        }

        current.set(Style.RIGHT_BUTTON, bsmt_button);
    }
}
