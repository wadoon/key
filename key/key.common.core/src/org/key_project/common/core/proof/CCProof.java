// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package org.key_project.common.core.proof;

import java.io.File;
import java.io.IOException;

import org.key_project.common.core.logic.Named;
import org.key_project.common.core.logic.NamespaceSet;
import org.key_project.common.core.services.CCServices;
import org.key_project.util.collection.ImmutableList;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 */
public interface CCProof<G extends CCGoal<?, ?, ?, ?, ?>> extends Named {

    File getJavaSourceLocation();

    void saveToFile(File file) throws IOException;

    void setProofFile(File proofFile);

    File getProofFile();

    void pruneProof(G goal);

    boolean closed();

    void add(ImmutableList<G> goals);

    void add(G goal);

    void reOpenGoal(G p_goal);

    void closeGoal(G p_goal);

    void replace(G oldGoal, ImmutableList<G> newGoals);

    ImmutableList<G> openEnabledGoals();

    ImmutableList<G> openGoals();

    void setNamespaces(NamespaceSet ns);

    void addAutoModeTime(long time);

    long getAutoModeTime();

    CCServices<?, ?, ?, ?> getServices();

    NamespaceSet getNamespaces();

    String header();

    boolean isDisposed();

    void dispose();

}
