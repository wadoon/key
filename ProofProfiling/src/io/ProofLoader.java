package io;

import java.io.File;
import java.nio.file.Path;
import java.nio.file.Paths;
import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

public class ProofLoader {

	private Proof proof = null;

	private Path path;

	public ProofLoader(String path) {
		this.path = Paths.get(path);
	}

	public Proof getProof() {
		if (proof == null) {
			AbstractUserInterfaceControl uiCtrl = new DefaultUserInterfaceControl();
			try {
				Profile profile = AbstractProfile.getDefaultProfile();
				File file = path.toFile();
				AbstractProblemLoader result = uiCtrl.load(profile, file, null, null, null, null, false);
				proof = result.getProof();
			} catch (ProblemLoaderException e) {
				e.printStackTrace();
			}
		}
		return proof;
	}

}
