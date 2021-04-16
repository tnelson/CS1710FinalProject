//Get all the data out of Sterling
const allinst = instances.map(instanceToGraph)
var maindiv = getElem("stagediv","div")
console.log(maindiv)

maindiv.innerHTML = ''
document.body.append(maindiv); 
var e = getElem("proctable","table")
maindiv.appendChild(e) ; 
console.log(e)
createInstTable(allinst[0])
function getElem(eid,tp) { 
  var el = document.getElementById(eid) ; 
  if(!el) {
    el = document.createElement(tp) 
    el.id = eid
  }
  return el ; 
}

function createInstTable(inst) { 
    let table = document.querySelector("table");
    console.log(table)
    function generateTableHead(table) {
      var tableheaders = ["Process ID","Process","State","PageTable","Pages"]
      let thead = table.createTHead();
      let row = thead.insertRow();
      for (let key of tableheaders) {
      let th = document.createElement("th");
      let text = document.createTextNode(key);
      th.appendChild(text);
      row.appendChild(th);
      }
}
     generateTableHead(table)
    function createProcTable(proc) { 

    
    }


}

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
    perms: p.join(proc_ptb.join(permissions)).tuples().map(e => {return [e.atoms()[0].id(),e.atoms()[1].id()]}),
    proc_state: p.join(proc_st).tuples().map(e => {return e.atoms()[0].id()})
  }
  }
  const allprocs = procs.map(getProcess) ; 
  function getPages(mp) {
    const pgdr = mp.atoms()[1].id()  ; 
    const pgArr = new Array() ; 
    for(const proc of allprocs) { 
      if(proc.proc_pages.includes(pgdr) ){
        pgArr.push(proc.pname)
      }
    }
    return {
      pagename:mp.atoms()[0].id(),
      addr: pgdr ,
      page_procs:pgArr
    }
  }
  const pgs = padr.tuples().map(getPages) ; 
  return {
    process:allprocs,
    pages:pgs
  } 
  
}