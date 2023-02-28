package io.kaitai.struct

import io.kaitai.struct.datatype.DataType
import io.kaitai.struct.datatype.DataType._
import io.kaitai.struct.datatype.{Endianness, FixedEndian, InheritedEndian}
import io.kaitai.struct.format._
import io.kaitai.struct.languages.TypeScriptCompiler
import io.kaitai.struct.languages.components.ExtraAttrs

import scala.collection.mutable

class TypeScriptClassCompiler(
  classSpecs: ClassSpecs,
  override val topClass: ClassSpec,
  config: RuntimeConfig
) extends ClassCompiler(classSpecs, topClass, config, TypeScriptCompiler) {
  override def compileSubclasses(curClass: ClassSpec): Unit =
    curClass.types.foreach { case (_, intClass) => {
      compileClass(intClass)
      compileNamespaces(intClass)
  }}

  def isExternalClass(curClass: ClassSpec): Boolean = curClass.name.head != topClass.name.head

  def getExternalDataTypes(dataType: DataType): Iterable[ClassSpec] = {
    dataType match {
      case ut: UserType =>
        val curClass = ut.classSpec.get
        if (isExternalClass(curClass)) {
          List(curClass)
        } else {
          List()
        }
      case st: SwitchType =>
        st.cases.flatMap { case (_, ut) =>
          getExternalDataTypes(ut)
        }
      case _ =>
        List()
    }
  }

  def importExternalClasses(curClass: ClassSpec) = {
    val externalClasses = mutable.Set[ClassSpec]()
    curClass.seq.map((attr) =>
      externalClasses ++= getExternalDataTypes(attr.dataType)
    )

    curClass.params.foreach((paramDefSpec) =>
      externalClasses ++= getExternalDataTypes(paramDefSpec.dataType)
    )

    curClass.instances.foreach { case (_, inst) =>
      inst match {
        case pis: ParseInstanceSpec =>
          externalClasses ++= getExternalDataTypes(pis.dataType)
        case _ => None
      }
    }

    externalClasses.foreach(lang.opaqueClassDeclaration)
  }

  override def compileClass(curClass: ClassSpec): Unit = {
    provider.nowClass = curClass

    importExternalClasses(curClass)

    // documentation
    compileClassDoc(curClass)
    
    lang.classHeader(curClass.name)

    provider.nowClass = curClass

    val narrowAttrs: List[AttrSpec] = List(
      AttrSpec(List(), IoIdentifier, KaitaiStreamType),
      AttrSpec(List(), RootIdentifier, CalcUserType(topClassName, None)),
    ) ++ (curClass.parentType match {
      case KaitaiStructType | CalcKaitaiStructType => List()
      case _ =>
        List(AttrSpec(List(), ParentIdentifier, curClass.parentType))
    })

    // public <attrname>: <attrtype>;
    val allAttrs: List[MemberSpec] =
      curClass.seq ++
      curClass.params ++
      narrowAttrs ++
      ExtraAttrs.forClassSpec(curClass, lang)
    compileAttrDeclarations(allAttrs)
    compileAttrReaders(allAttrs)

    // constructor() {...}
    compileConstructor(curClass)

    compileEagerRead(curClass.seq, curClass.meta.endian)

    // private <private instance name>: ...;
    // get <public instance name>() {...}
    compileInstances(curClass)
    
    curClass.toStringExpr.foreach(expr => lang.classToString(expr))

    // }
    lang.classFooter(curClass.name)

    if (curClass == topClass) {
      compileNamespaces(curClass);
    }
  }

  override def compileInstance(className: List[String], instName: InstanceIdentifier, instSpec: InstanceSpec, endian: Option[Endianness]): Unit = {
    // Determine datatype
    val dataType = instSpec.dataTypeComposite

    compileInstanceDeclaration(instName, instSpec)

    if (!lang.innerDocstrings)
      compileInstanceDoc(instName, instSpec)
    lang.instanceHeader(className, instName, dataType, instSpec.isNullable)
    if (lang.innerDocstrings)
      compileInstanceDoc(instName, instSpec)
    lang.instanceCheckCacheAndReturn(instName, dataType)

    instSpec match {
      case vi: ValueInstanceSpec =>
        lang.attrParseIfHeader(instName, vi.ifExpr)
        lang.instanceCalculate(instName, dataType, vi.value)
        lang.attrParseIfFooter(vi.ifExpr)
        lang.instanceSetCalculated(instName)
      case pi: ParseInstanceSpec =>
        lang.attrParse(pi, instName, endian)
    }

    if (instSpec.isNullable)
      lang.asInstanceOf[TypeScriptCompiler].instanceEnsureNull(instName)

    lang.instanceReturn(instName, dataType)
    lang.instanceFooter
  }

  def compileNamespaces(curClass: ClassSpec): Unit = {
    val compiler = lang.asInstanceOf[TypeScriptCompiler];
    if (curClass.enums.size > 0 || curClass.types.size > 0) {
      // namespace thing {...
      compiler.namespaceHeader(curClass.name)

      // static <enum name> = Object.freeze({...})
      compileEnums(curClass)

      compileSubclasses(curClass)

      compiler.namespaceFooter(curClass.name)
    }
  }

  override def compileSeq(seq: List[AttrSpec], defEndian: Option[FixedEndian]) = {
    var wasUnaligned = false
    seq.foreach { (attr) =>
      val nowUnaligned = isUnalignedBits(attr.dataType)
      if (wasUnaligned && !nowUnaligned)
        lang.alignToByte(lang.normalIO)
      lang.attrParse(attr, attr.id, defEndian)
      wasUnaligned = nowUnaligned
    }
  }
}
