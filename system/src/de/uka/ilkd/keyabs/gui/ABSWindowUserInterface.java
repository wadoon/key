package de.uka.ilkd.keyabs.gui;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.WindowUserInterface;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.util.KeYRecoderExcHandler;
import de.uka.ilkd.keyabs.init.ABSProblemInitializer;

public class ABSWindowUserInterface extends WindowUserInterface {

    public ABSWindowUserInterface(MainWindow mainWindow) {
        super(mainWindow);
    }

    public ABSProblemInitializer createProblemInitializer() {
        Profile profile = getMediator().getProfile();
        return new ABSProblemInitializer(this, profile, 
                profile.createServices(new KeYRecoderExcHandler()), true, this);
    }
}
