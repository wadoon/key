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

package de.uka.ilkd.key.proof;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.logic.Name;

public class NameRecorder {

    private ImmutableList<Name> pre = ImmutableSLList.<Name>nil();

    private ImmutableList<Name> post = ImmutableSLList.<Name>nil();

    public ImmutableList<Name> getProposals() {
        return post;
    }

    public void addProposal(Name proposal) {
        synchronized(post) {
            post = post.append(proposal);
        }
    }

    public void setProposals(ImmutableList<Name> proposals) {
        synchronized(pre) {
            pre = proposals;
        }
    }

    public Name getProposal() {
        synchronized(pre) {
            Name proposal = null;

            if (pre != null && !pre.isEmpty()) {
                proposal = pre.head();
                pre = pre.tail();
            }

            return proposal;
        }
    }

    public NameRecorder copy() {
        final NameRecorder result = new NameRecorder();
        synchronized(pre) {
            synchronized(post) {
                result.pre = pre;
                result.post = post;
                return result;
            }
        }
    }
}