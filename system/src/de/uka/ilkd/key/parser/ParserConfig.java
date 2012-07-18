// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.parser;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.logic.NamespaceSet;

public class ParserConfig<S extends IServices> {

    private S services;
    private NamespaceSet nss;

    
    public ParserConfig(S services, 
			NamespaceSet nss) {
	this.services = services;
	this.nss      = nss;
    }


    public S services() {
	return services;
    }

    public NamespaceSet namespaces() {
	return nss;
    }

/*    public KeYRecoderMapping keyRecoderMapping() {
	return services.getJavaInfo().rec2key();
    }

    public TypeConverter typeConverter() {
	return services.getTypeConverter();
    }

    public KeYCrossReferenceServiceConfiguration serviceConfiguration() {
	return services.getJavaInfo().
	    getKeYProgModelInfo().getServConf();
    } */

}
