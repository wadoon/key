parser grammar KeYCommonParser;

options {
    tokenVocab = KeYCommonLexer;
}

@header {
	package org.key_project.common.core.parser;
}

init: ID*? ;
