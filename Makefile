all: AlphaRen.vo LetrecEx.vo SubstAuxAlphaEq.vo SSubst.vo AlphaDecider.vo



AlphaDecider.vo : AlphaDecider.v AlphaEqProps.vo 
	coqc $<

SubstAux.vo : SubstAux.v Term.vo
	coqc $<

SSubst.vo : SSubst.v AlphaRen.vo SubstAuxAlphaEq.vo
	coqc $<

SubstAuxAlphaEq.vo : SubstAuxAlphaEq.v SubstAux.vo AlphaEqProps.vo
	coqc $<

#AssociationList.vo : AssociationList.v ./list.vo
#	coqc AssociationList.v

nuprlGrammarUnconstrained.vo : nuprlGrammarUnconstrained.v CFGV.vo SubstAux.vo
	coqc nuprlGrammarUnconstrained.v

#StringGrammar.vo:	CFGV.vo StringGrammar.v FinSetList.vo
#	coqc StringGrammar.v

CFGV.vo:	CFGV.v GVariables.vo
	coqc CFGV.v

GSubst.vo:	GSubst.v AlphaEqProps.vo SubstAux.vo
	coqc $<

AlphaRen.vo:	AlphaRen.v AlphaEqProps.vo
	coqc $<

Term.vo:	Term.v CFGV.vo
	coqc $<

LetrecEx.vo:	LetrecEx.v Term.vo AlphaDecider.vo
	coqc $<

LetrecFEx.vo:	LetrecFEx.v Term.vo
	coqc $<

AlphaEquality.vo:	AlphaEquality.v Swap.vo
	coqc $<

AlphaEqProps.vo:	AlphaEqProps.v AlphaEquality.vo SwapProps.vo
	coqc $<

Swap.vo:	Swap.v Term.vo
	coqc $<

SwapProps.vo:	SwapProps.v Swap.vo
	coqc $<

papertex: Term.tex GVariables.tex CFGV.tex SubstAux.tex Swap.tex SSubst.tex AlphaEquality.tex LetrecEx.tex LetrecFEx.tex

paperRtex: Term.rtex SubstAux.rtex Swap.rtex SSubst.rtex AlphaEquality.rtex GVariables.rtex

%.html :  %.vo
	coqdoc $*.v --interpolate -utf8

GVariables.vo : 	GVariables.v ./variables.vo ./AssociationList.vo
	coqc GVariables.v


FinSetList.vo : 	FinSetList.v
	coqc FinSetList.v

parent : 
	make -j3 -C ./ AssociationList.vo variables.vo

Term.dreplace : CFGV.replace All.replace
	cat CFGV.replace > $(@)
	cat All.replace >> $(@)

Swap.dreplace : CFGV.replace All.replace
	cat CFGV.replace > $(@)
	cat All.replace >> $(@)

AlphaEquality.dreplace : Term.replace Swap.replace CFGV.replace All.replace
	cat CFGV.replace > $(@)
	cat Term.replace >> $(@)
	cat Swap.replace >> $(@)
	cat All.replace >> $(@)

SSubst.dreplace : CFGV.replace SAuxRen.replace Term.replace All.replace
	cat CFGV.replace > $(@)
	cat Term.replace >> $(@)
	cat SAuxRen.replace >> $(@)
	cat All.replace >> $(@)


SubstAux.dreplace : CFGV.replace Term.replace All.replace
	cat CFGV.replace > $(@)
	cat Term.replace >> $(@)
	cat All.replace >> $(@)

CFGV.dreplace : GVariables.replace All.replace
	cat GVariables.replace > $(@)
	cat All.replace >> $(@)

GVariables.dreplace : All.replace
	cat All.replace > $(@)


parent2 : 
	make -j3 -C ./ alphaeq.vo

%.tex: %.vo
	coqdoc   -l --latex --interpolate --body-only $(basename $<).v -o $(@)

%.rtex: %.dreplace
	java -jar searchreplace.jar $< $(basename $<).tex

#.PHONY: parent
htmls : CFGV.html SubstAux.html AlphaEquality.html SwapProps.html Swap.html AlphaEqProps.html SubstAuxAlphaEq.html Term.html AlphaRen.html SSubst.html AlphaDecider.html GVariables.html LetrecEx.html
	make -C ./ UsefulTypes.html list.html universe.html AssociationList.html
	cp ./UsefulTypes.html ./
	cp ./list.html ./
	cp ./universe.html ./
	cp ./AssociationList.html ./

clean :
	rm *.vo *.glob

list.vo : list.v UsefulTypes.vo bin_rels.vo
	coqc list.v

AssociationList.vo : list.vo AssociationList.v
	coqc AssociationList.v

variables.vo : variables.v list.vo
	coqc variables.v

tactics.vo : tactics.v eq_rel.vo LibTactics.vo
	coqc tactics.v

UsefulTypes.vo : UsefulTypes.v tactics.vo
	coqc UsefulTypes.v

LibTactics.vo : LibTactics.v
	coqc LibTactics.v

eq_rel.vo : eq_rel.v universe.vo
	coqc eq_rel.v

bin_rels.vo : bin_rels.v UsefulTypes.vo
	coqc bin_rels.v

universe.vo : universe.v
	coqc universe.v

