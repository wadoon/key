package de.uka.ilkd.key.nui.view.menu;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import javafx.scene.control.MenuItem;

/**
 * A menu item with a TacletApp connected to it.
 * 
 * @author Victor Schuemmer
 */
public class TacletMenuItem extends MenuItem {

    private TacletApp tacletApp;

    /**
     * @return the TacletApp connected to the menu item
     */
    public TacletApp getTacletApp() {
        return tacletApp;
    }

    /**
     * Convenience method to directly access the Taclet associated with the
     * connected TacletApp
     * 
     * @return the Taclet associated with the connected TacletApp
     */
    public Taclet getTaclet() {
        return tacletApp.taclet();
    }

    private NotationInfo notationInfo;

    /**
     * @return the notationInfo that was passed to the constructor
     */
    public NotationInfo getNotationInfo() {
        return notationInfo;
    }

    private Services services;

    /**
     * @return the services that were passed to the constructor
     */
    public Services getServices() {
        return services;
    }

    /**
     * Constructs a menu item with a TacletApp connected to it.
     * 
     * @param tacletApp
     *            the TacletApp to connect with the menu item. The item's text
     *            will be set to the TacletApp's displayName.
     * @param notationInfo
     * @param services
     */
    public TacletMenuItem(TacletApp tacletApp, NotationInfo notationInfo,
            Services services) {
        super(tacletApp.taclet().displayName());
        this.tacletApp = tacletApp;
        this.notationInfo = notationInfo;
        this.services = services;
    }

    /**
     * Fires the item's action programmatically.
     */
    public void performAction() {
        fire();
    }

    @Override
    public String toString() {
        return tacletApp.taclet().displayName();
    }
}
