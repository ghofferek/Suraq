package at.iaik.suraq.parser;

import java.io.BufferedReader;
import java.io.IOException;
import java.text.ParseException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Set;
import java.util.Stack;


import at.iaik.suraq.exceptions.IncomparableTermsException;
import at.iaik.suraq.proof.VeritProof;
import at.iaik.suraq.proof.VeritProofSet;
import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.EqualityFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.Term;
import at.iaik.suraq.util.DebugHelper;
import at.iaik.suraq.util.FormulaCache;


public class VeriTParser extends Parser {
    
    protected final BufferedReader reader;
    protected final HashMap<String, Formula> macroBuffer = new HashMap<String, Formula>();

    //protected final Formula oldTopLevelFormula;
    protected final Set<PropositionalVariable> propositionalVariables;
    protected final Set<DomainVariable> domainVariables;
    

    protected final VeritProof proof = new VeritProof();
    
    public VeriTParser(BufferedReader reader, Formula oldTopLevelFormula, Set<PropositionalVariable> tseitinVars)
    {
        assert(reader != null);
        this.reader = reader;

        //this.oldTopLevelFormula = oldTopLevelFormula;
        this.domainVariables = oldTopLevelFormula.getDomainVariables();
        this.propositionalVariables = oldTopLevelFormula.getPropositionalVariables();
        propositionalVariables.addAll(tseitinVars);
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

                System.out.println(" Line "+lines+ " contains '"+name+"' has length of "+ line.length());
                System.out.println(" Rest: '"+rest+"'");
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
                
                System.out.println(" clauses: '"+parsed_clauses+"'");
                System.out.println(" iargs: '"+parsed_iargs+"'");
                System.out.println(" conclusion: '"+conclusion+"'");
                
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
    
    protected ArrayList<Formula> parseConclusion(String conclusion, int lineNumber) throws ParseException, IncomparableTermsException
    {
        int length = conclusion.length();
        ArrayList<Formula> conclusions = new ArrayList<Formula>();
        boolean macro_name = false;
        Stack<String> macronames = new Stack<String>();
        Stack<String> commandStack = new Stack<String>();
        Stack<ArrayList<Formula>> formulaStack = new Stack<ArrayList<Formula>>();
        Stack<ArrayList<Term>> termStack = new Stack<ArrayList<Term>>();
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
                    Formula formula = macroBuffer.get(str.toString());
                    if(formula == null)
                    {
                        throw new ParseException("Macro #"+str+" was not declared before (line="+lineNumber+").", lineNumber);
                    }
                    formulaStack.peek().add(formula);
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
                        // its a variable
                        Term term = findVariable(tmp);
                        if(term instanceof PropositionalVariable)
                            formulaStack.peek().add((PropositionalVariable)term);
                        // DomainVariable and PropositionalVariable
                        termStack.peek().add(term);
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
            }
            else if(cur == ')')
            {
                macronames.pop();
                String macroname = null;
                if(macronames.size() != 0)
                    macroname = macronames.peek();
                ArrayList<Formula> formulaElements = formulaStack.pop();
                ArrayList<Term> termElements = termStack.pop();
                String command = commandStack.pop();
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
                        //macroBuffer.put(macroname,formulaStack.peek().get(formulaStack.size()-1));
                        
                        macroBuffer.put(macroname,formulaStack.peek().get(formulaStack.peek().size()-1));
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
    
    protected Term findVariable(String name)
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
    
    
    
    
}
