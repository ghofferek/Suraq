package at.iaik.suraq.parser;

import java.io.BufferedReader;
import java.text.ParseException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import at.iaik.suraq.exceptions.IncomparableTermsException;
import at.iaik.suraq.exceptions.WrongFunctionTypeException;
import at.iaik.suraq.exceptions.WrongNumberOfParametersException;
import at.iaik.suraq.proof.VeritProof;
import at.iaik.suraq.proof.VeritProofSet;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.ArrayVariable;
import at.iaik.suraq.smtlib.formula.DomainTerm;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.EqualityFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.Term;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;
import at.iaik.suraq.smtlib.formula.UninterpretedFunctionInstance;
import at.iaik.suraq.smtlib.formula.UninterpretedPredicateInstance;
import at.iaik.suraq.util.DebugHelper;


public class VeriTParser extends Parser {
    
    private final BufferedReader reader;
    private final HashMap<String, Formula> macroBufferFormula = new HashMap<String, Formula>();
    private final HashMap<String, Term> macroBufferTerm = new HashMap<String, Term>();

    //private final Formula oldTopLevelFormula;
    private final Set<PropositionalVariable> propositionalVariables;
    private final Set<DomainVariable> domainVariables;
    private final Set<String> uninterpretedFunctionNames;
    private final Set<UninterpretedFunction> uninterpretedFunctions;
    

    private final VeritProof proof = new VeritProof();
    
    public VeriTParser(BufferedReader reader, Formula oldTopLevelFormula,
            Set<PropositionalVariable> tseitinVars,
            Collection<List<Term>> noDependenceVarsCopies,
            Map<Token, List<UninterpretedFunction>> noDependenceFunctionsCopies) {
        assert (reader != null);
        this.reader = reader;

        // this.oldTopLevelFormula = oldTopLevelFormula;
        this.domainVariables = oldTopLevelFormula.getDomainVariables();
        this.propositionalVariables = oldTopLevelFormula
                .getPropositionalVariables();
        this.uninterpretedFunctionNames = oldTopLevelFormula
                .getUninterpretedFunctionNames();
        this.uninterpretedFunctions = oldTopLevelFormula
                .getUninterpretedFunctions();

        propositionalVariables.addAll(tseitinVars);
        for (List<Term> terms : noDependenceVarsCopies) {
            for (Term term : terms) {
                if (term instanceof DomainVariable)
                    this.domainVariables.add((DomainVariable) term);
                else if (term instanceof PropositionalVariable)
                    this.propositionalVariables
                            .add((PropositionalVariable) term);
                else if (term instanceof ArrayVariable)
                    throw new RuntimeException(
                            "Didn't expect array variables here.");
                else
                    throw new RuntimeException(
                            "Unknown type of noDependenceVarCopies");
            }
        }

        for (List<UninterpretedFunction> ufs : noDependenceFunctionsCopies
                .values()) {
            for (UninterpretedFunction uf : ufs) {
                uninterpretedFunctions.add(uf);
                uninterpretedFunctionNames.add(uf.getName().toString());
            }
        }
    }
    
    
    @Override
    public void parse() 
    {
        int lines = 0;
        try {
            String line = reader.readLine();
            while(line != null)
            {
                lines++;
                // parse here
                if(!line.startsWith("(set ."))
                    throw new ParseException(line, lines);
                
                
                int pos_begin = "(set ".length();
                int pos_end = line.indexOf(' ',pos_begin);
                String name = line.substring(pos_begin, pos_end);
                // rest = (input :conclusion (#1:(and (not #2:(= lambda_....)) excl. surrounding brackets
                String rest = line.substring(pos_end + 2, line.length()-1);

                //System.out.println(" Line "+lines+ " contains '"+name+"' has length of "+ line.length());
                //System.out.println(" Rest: '"+rest+"'");
                pos_end = rest.indexOf(' ',0);
                String type = rest.substring(0,pos_end); // input, and, or, resolution, eq_transitive,...

                int pos_clauses = rest.indexOf(":clauses ",0);
                int pos_iargs = rest.indexOf(":iargs ",0);
                int pos_conclusion = rest.indexOf(":conclusion ",0);
                
                String clauses = null;
                String[] parsed_clauses = null;
                String iargs = null;
                Integer parsed_iargs = null;
                String conclusion = null;
                ArrayList<VeritProofSet> parsed_clauses2 = null;
                
                // content of :* without :* and without brackets
                if(pos_clauses > 0 )
                {
                    int until = (pos_iargs>0) ? pos_iargs : pos_conclusion;
                    clauses = rest.substring(pos_clauses + ":clauses (".length(), until-2);
                    parsed_clauses = clauses.split("\\s"); // \s=A whitespace character: [ \t\n\x0B\f\r]
                    parsed_clauses2 = new ArrayList<VeritProofSet>();
                    for(String parsed_clause : parsed_clauses)
                    {
                        parsed_clauses2.add(proof.getProofSet(parsed_clause));
                    }
                }
                if(pos_iargs > 0)
                {
                    iargs = rest.substring(pos_iargs + ":iargs (".length(), pos_conclusion-2);
                    parsed_iargs = Integer.parseInt(iargs);
                }
                // conclusion WITH brackets!
                conclusion = rest.substring(pos_conclusion + ":conclusion ".length(), rest.length()-1);
                if(conclusion.length()==0)
                    conclusion = null;
                
                //System.out.println(" clauses: '"+parsed_clauses+"'");
                //System.out.println(" iargs: '"+parsed_iargs+"'");
                //System.out.println(" conclusion: '"+conclusion+"'");
                
                ArrayList<Formula> conclusions = parseConclusion(conclusion, lines);
                //System.out.println("Parsed Conclusions: "+ conclusions.toString());
                
                //DebugHelper.getInstance().stringtoFile(conclusions.toString(), "~verit_z"+lines+".tmp");
                proof.addProofSet(name, type, conclusions, parsed_clauses2, parsed_iargs);
                
                // read next line
                line = reader.readLine();
            }
            parsingSuccessfull = true;
            
        } catch (Exception e) {
            parsingSuccessfull = false;
            System.err.println("Error parsing line " + lines);
            e.printStackTrace();
            throw new RuntimeException(e);
        }
        finally
        {
            System.out.println("There were "+lines+" lines.");
        }
    }
    
    private ArrayList<Formula> parseConclusion(String conclusion, int lineNumber) throws ParseException, IncomparableTermsException
    {
        try{
        int length = conclusion.length();
        ArrayList<Formula> conclusions = new ArrayList<Formula>();
        boolean macro_name = false;
        Stack<String> macronames = new Stack<String>();
        Stack<String> commandStack = new Stack<String>();
        Stack<ArrayList<Formula>> formulaStack = new Stack<ArrayList<Formula>>();
        Stack<ArrayList<Term>> termStack = new Stack<ArrayList<Term>>();
        Stack<UninterpretedFunction> uninterpretedStack = new Stack<UninterpretedFunction>();
        StringBuilder str = new StringBuilder();
        
        for(int i=0;i<length; i++)
        {
            char cur = conclusion.charAt(i);

            if(cur == ' ' || cur == ')')
            {
                if(macro_name)
                {
                    // we got #12macroname
                    // find a pre-defined formula, that originaly was defined by #12:...
                    macro_name = false;
                    Formula formula = macroBufferFormula.get(str.toString());
                    Term term = macroBufferTerm.get(str.toString());
                    if(formula != null)
                    {
                        formulaStack.peek().add(formula);
                    }
                    if(term != null)
                    {
                        termStack.peek().add(term);
                    }
                    if(term == null && formula == null)
                    {
                        throw new ParseException("Macro #"+str+" was not declared before (line="+lineNumber+").", lineNumber);
                    }
                }
                else 
                {
                    // it's a variable or a command
                    String tmp = str.toString();
                    if(tmp.equals("and") || tmp.equals("or") || tmp.equals("=") || tmp.equals("not"))
                    {
                        // it is a command: and, or, =
                        commandStack.pop();
                        commandStack.push(tmp);
                    }
                    else if(tmp.length()>0)
                    {
                        if(uninterpretedFunctionNames.contains(tmp))
                        {
                            // its an uninterpreted function, save it
                            uninterpretedStack.pop();
                            uninterpretedStack.push(findUninterpretedFunction(tmp));
                        }
                        else
                        {
                            // its a variable
                            Term term = findVariable(tmp);
                            if(term instanceof PropositionalVariable)
                                formulaStack.peek().add((PropositionalVariable)term);
                            // DomainVariable and PropositionalVariable
                            termStack.peek().add(term);
                        }
                    }
                }
            }
            if(cur == ' ')
            {
                // handled above
            }
            else if(cur == '(')
            {
                formulaStack.push(new ArrayList<Formula>());
                termStack.push(new ArrayList<Term>());
                commandStack.push(null);
                macronames.push(null);
                uninterpretedStack.push(null);
            }
            else if(cur == ')')
            {
                String macroname = null;
                macronames.pop();
                if(macronames.size() != 0)
                    macroname = macronames.peek();
                String command = commandStack.pop();
                
                
                boolean was_uf = false;
                UninterpretedFunction uf = uninterpretedStack.pop();
                if(uf != null)
                {
                    // generate a new UninterpretedFunctionInstance or UninterpretedPredicateInstance
                    // with the parameters stored in formulaElements
                    ArrayList<DomainTerm> formulaElements = new ArrayList<DomainTerm>();
                    for(Term tmp3 : termStack.pop())
                        formulaElements.add((DomainTerm)tmp3);
                    formulaStack.pop();
                    // formulaStack.push(new ArrayList<Formula>());
                    
                    Term newTerm = null;
                    if(uf.getType().equalsString("Value"))
                    {
                        newTerm = UninterpretedFunctionInstance.create(uf, formulaElements);

                        if(macroname != null)
                        {
                            System.out.println("[M] Stored macro #"+macroname);
                            macroBufferTerm.put(macroname, (UninterpretedFunctionInstance)newTerm);
                        }
                    }
                    else if(uf.getType().equalsString("Bool"))
                    {
                        newTerm = UninterpretedPredicateInstance.create(uf, formulaElements);
                        //ArrayList<Formula> newFormulas = new ArrayList<Formula>();
                        //newFormulas.add((UninterpretedPredicateInstance)newTerm);
                        //formulaStack.push(newFormulas);
                        formulaStack.peek().add((UninterpretedPredicateInstance)newTerm);

                        if(macroname != null)
                        {
                            System.out.println("[M] Stored macro #"+macroname);
                            macroBufferFormula.put(macroname, (UninterpretedPredicateInstance)newTerm);
                            macroBufferTerm.put(macroname, (UninterpretedPredicateInstance)newTerm);
                        }
                    }
                    else
                        assert(false);
                    // store to terms:
                    //ArrayList<Term> newTerms = new ArrayList<Term>();
                    //newTerms.add(newTerm);
                    //termStack.push(newTerms);
                    termStack.peek().add(newTerm);
                    
                    was_uf = true;
                }
                if(!was_uf)
                {
                    ArrayList<Formula> formulaElements = formulaStack.pop();
                    ArrayList<Term> termElements = termStack.pop();
                    if(command != null)
                    {
                        if(command.equals("not"))
                        {
                            if(formulaElements.size()!=1)
                                throw new ParseException("Not has not 1 element. #Elements="+formulaElements.size(),lineNumber);
                            formulaStack.peek().add(NotFormula.create(formulaElements.get(0)));
                        }
                        else if(command.equals("="))
                        {
                            EqualityFormula formula;
                            formula = EqualityFormula.create(termElements, true);
                            formulaStack.peek().add(formula);
                        }
                        else if(command.equals("and"))
                        {
                            formulaStack.peek().add(AndFormula.generate(formulaElements));
                        }
                        else if(command.equals("or"))
                        {
                            formulaStack.peek().add(OrFormula.generate(formulaElements));
                        }
                        else
                        {
                            throw new ParseException("Unknown Command", lineNumber);
                        }
                        if(macroname != null)
                        {
                            System.out.println("[M] Stored macro #"+macroname);
                            macroBufferFormula.put(macroname,formulaStack.peek().get(formulaStack.peek().size()-1));
                            if(formulaStack.peek().get(formulaStack.peek().size()-1) instanceof Term)
                                macroBufferTerm.put(macroname,(Term)formulaStack.peek().get(formulaStack.peek().size()-1));
                        }
                    }
                    else
                    {
                        // just a list of variables
                        if(commandStack.size() == 0)
                        {
                            // this is the :conclusion layer
                            conclusions.addAll(formulaElements);
                        }
                        else
                        {
                            throw new ParseException("We have a list of Variables without command.", lineNumber);
                        }
                    }
                }
            }
            else if(cur == '#') // #2 or #2:
            {
                // define, that the following string (until : or space) will be a macro
                macro_name = true;
            }
            else if(cur == ':')
            {
                macro_name = false;
                // define a macro to be defined on that layer, when returning from (
                macronames.pop();
                macronames.push(str.toString());
            }
            else
            {
                str.append(cur);
                continue;
            }
            // clear the buffer:
            str.setLength(0);
        }
        return conclusions;
        }
        catch(Exception e)
        {
            throw new RuntimeException(e);
        }
    }
    
    private UninterpretedFunction findUninterpretedFunction(String name)
    {
        if(this.uninterpretedFunctionNames.contains(name))
        {
            UninterpretedFunction uf = null;
            for(UninterpretedFunction tmp : uninterpretedFunctions)
            {
                // NOTE: please do not use the same name for different count of parameters or different types
                if(tmp.getName().equalsString(name))
                {
                    uf = UninterpretedFunction.create(tmp.getName(), tmp.getNumParams(), tmp.getType());
                    break;
                }
            }
            if(uf != null)
                return uf;
        }
        String err = "Unknown Variable '"+name+"' on parsing. Cannot decide if it is a propositional or domain variable.";
        System.err.println(err);
        throw new RuntimeException(err);
    }
    
    private Term findVariable(String name)
    {
        if(this.domainVariables.contains(DomainVariable.create(name)))
        {
            return DomainVariable.create(name);
        }
        else if(this.propositionalVariables.contains(PropositionalVariable.create(name)))
        {
            return PropositionalVariable.create(name);
        }
        String err = "Unknown Variable '"+name+"' on parsing. Cannot decide if it is a propositional or domain variable.";
        System.err.println(err);
        throw new RuntimeException(err);
    }
    
    public VeritProof getProof()
    {
        return proof;
    }
    
    
}
