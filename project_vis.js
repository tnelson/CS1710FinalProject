instanceToGraph(instances[0]) ; 


function instanceToGraph(inst) { 
  //The States 
  const states = inst.signature("State").atoms(true) ; 
const procs = inst.signature('Process').atoms(true) ;
  const pages = inst.signature("Page").atoms() ; 
  const pagetables = inst.signature('Pagetable').atoms() ; 
  //Process fields 
  const pid = inst.field('pid') ; 
  const proc_ptb  = inst.field('ptable') ; 
  const proc_st = inst.field('st') ; 
  //Pagetable fields
  const mapping = inst.field('mapping') ; 
  const permissions = inst.field('permissions') ; 
  //Page fields 
  const padr = inst.field("address") ; 
  const next = inst.field("next") ; 
  function getProcess(p) { 
  return {
    pname : p.id() , 
    proc_id : p.join(pid).tuples()[0].atoms()[0].id() , 
    proc_tbl : p.join(proc_ptb).tuples().map(e => {return e.atoms()[0].id()}) , 
    proc_pages: p.join(proc_ptb).join(mapping).tuples().map(e => {return e.atoms()[0].id()}) , 
    perms: p.join(proc_ptb.join(permissions)).tuples().map(e => {return [e.atoms()[0].id(),e.atoms()[1].id()]})
  }
  }
  const all_procs = procs.map(getProcess) ; 
  console.log(all_procs)
  
}