// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.init;

import java.io.File;
import java.io.IOException;

import org.antlr.runtime.RecognitionException;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.parser.KeYParserF;
import de.uka.ilkd.key.parser.ParserConfig;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.proof.io.KeYFile;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.SLEnvInput;
import de.uka.ilkd.key.util.ProgressMonitor;
import de.uka.ilkd.key.util.Triple;


/** 
 * Represents an input from a .key user problem file producing an environment
 * as well as a proof obligation.
 */
public final class KeYUserProblemFile extends KeYFile {
    
    
    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    /** 
     * Creates a new representation of a KeYUserFile with the given name,
     * a rule source representing the physical source of the input, and
     * a graphical representation to call back in order to report the progress
     * while reading.
     */
    public KeYUserProblemFile(String name, 
                              File file, 
                              ProgressMonitor monitor,
                              Profile profile) {
        super(name, file, monitor, profile);
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
        
    @Override
    public ImmutableSet<PositionedString> read() throws ProofInputException {
        if(initConfig == null) {
            throw new IllegalStateException("InitConfig not set.");
        }	
        
        //read activated choices
        KeYParserF problemParser = null;
        try {

        	ProofSettings settings = getProofSettings();
            initConfig.setSettings(settings);	
        	
            ParserConfig pc = new ParserConfig
                (initConfig.getServices(), 
                 initConfig.namespaces());
            problemParser = new KeYParserF(ParserMode.PROBLEM, getKeYLexer(), pc);
            problemParser.parseWith();
            settings.getChoiceSettings()
                    .updateWith(problemParser.getActivatedChoices());
            initConfig.setActivatedChoices(settings.getChoiceSettings()
        	      		                   .getDefaultChoicesAsSet());
            
        } catch(RecognitionException e) {
            // problemParser cannot be null here
            String message = problemParser.getErrorMessage(e);
            throw new ProofInputException(message, e);
        } catch (Exception e) {
            throw new ProofInputException(e);      
        }     
	
        //read in-code specifications
        ImmutableSet<PositionedString> warnings = DefaultImmutableSet.nil();
        try {
        SLEnvInput slEnvInput = new SLEnvInput(readJavaPath(), 
        				       readClassPath(), 
        				       readBootClassPath(), getProfile(), null);
        
        slEnvInput.setInitConfig(initConfig);
        warnings = warnings.union(slEnvInput.read());
        } catch (IOException ioe) {
            throw new ProofInputException(ioe);
        } finally {
            closeLexerStream();
        }
                
        //read key file itself
        return warnings.union(super.read());
    }

    public boolean hasProofScript() {
        try {
        if(lastParser == null) {
            readProblem();
        }
        return lastParser.isAtProofScript();
        } catch (ProofInputException e) {
            return false;
        }
    }

    public Triple<String, Integer, Integer> readProofScript() throws ProofInputException {
        if (lastParser == null) {
            readProblem();
        }
        assert hasProofScript() : "Call this only if there is a proofScript!";
        try {
            return lastParser.proofScript();
        } catch (RecognitionException ex) {
            // problemParser cannot be null
            String message = lastParser.getErrorMessage(ex);
            throw new ProofInputException(message, ex);
        }
    }   
    
    @Override
    public boolean equals(Object o){
        if(o == null || o.getClass() != this.getClass()) {
            return false;
        }
        final KeYUserProblemFile kf = (KeYUserProblemFile) o;
        return kf.file.file().getAbsolutePath()
                             .equals(file.file().getAbsolutePath());
    }
    
    
    @Override
    public int hashCode() {
        return file.file().getAbsolutePath().hashCode();
    }

   /**
    * {@inheritDoc}
    */
   @Override
   public Profile getProfile() {
      return readProfileFromData();
   }
      
}
