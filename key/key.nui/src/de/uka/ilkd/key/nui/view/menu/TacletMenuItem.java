/**
 * 
 */
package de.uka.ilkd.key.nui.view.menu;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import javafx.scene.control.MenuItem;

/**
 * @author Victor Schuemmer
 *
 */
public class TacletMenuItem extends MenuItem {

    private TacletApp tacletApp;
    private NotationInfo notationInfo;
    private Services services;

    public TacletMenuItem(TacletApp tacletApp, NotationInfo notationInfo,
            Services services) {
        super(tacletApp.taclet().displayName());
        this.tacletApp = tacletApp;
        this.notationInfo = notationInfo;
        this.services = services;
    }

    public Taclet getTaclet() {
        return tacletApp.taclet();
    }

    public TacletApp getTacletApp() {
        return tacletApp;
    }

    public NotationInfo getNotationInfo() {
        return notationInfo;
    }
    
    public Services getServices() {
        return services;
    }
    
    public void performAction() {
        fire();
    }
    
    @Override
    public String toString() {
        return tacletApp.taclet().displayName();
    }
}
