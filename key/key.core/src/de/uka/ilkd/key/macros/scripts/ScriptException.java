package de.uka.ilkd.key.macros.scripts;

import java.io.File;
import java.util.List;

import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.rule.TacletApp;
import org.key_project.util.collection.ImmutableList;

@SuppressWarnings("serial")
public class ScriptException extends Exception {

    private final Location location;

    public ScriptException() {
        super();
        this.location = null;
    }

    public ScriptException(String message, String file, int line, int col, Throwable cause) {
        super(message, cause);
        if(file != null) {
            this.location = new Location(file, line, col);
        } else {
            this.location = null;
        }
    }

    public ScriptException(String message, String file, int line, int col) {
        super(message);
        if(file != null) {
            this.location = new Location(file, line, col);
        } else {
            this.location = null;
        }
    }


    public ScriptException(String message) {
        super(message);
        this.location = null;
    }

    public ScriptException(Throwable cause) {
        super(cause);
        this.location = null;
    }

    public ScriptException(String message, Throwable cause) {
        super(message, cause);
        this.location = null;
    }

    public Location getLocation() {
        return location;
    }



    static public class IndistinctFormula extends ScriptException {
        public List<TacletApp> getMatchingApps() {
            return matchingApps;
        }

        private List<TacletApp> matchingApps;
        public IndistinctFormula (List<TacletApp> matchingApps) {
            this.matchingApps = matchingApps;
        }
    }

    static public class MissingInstantiations extends ScriptException {
        public SchemaVariable getSv() {
            return sv;
        }

        private SchemaVariable sv;
        public MissingInstantiations (SchemaVariable sv) {
            this.sv = sv;
        }
    }

    static public class UnuniqueAssumesInstantiations extends ScriptException {
        public ImmutableList<TacletApp> getAssumesCandidates() {
            return assumesCandidates;
        }

        private ImmutableList<TacletApp> assumesCandidates;
        public UnuniqueAssumesInstantiations (ImmutableList<TacletApp> assumesCandidates) {
            this.assumesCandidates = assumesCandidates;
        }
    }


}
