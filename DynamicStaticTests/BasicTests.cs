using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using DynamicStatic;
using NUnit.Framework;

namespace DynamicStaticTests
{
    [TestFixture]
    public class BasicTests
    {
        [Test]
        public void FactorialDefinition()
        {
            Assert.AreEqual("(Atom -> Atom)", DS.type2str(DS.type_check(DS.fact)));
        }

        [Test]
        public void MapDefinition()
        {
            var actual = DS.type2str(DS.type_check(DS.map));
            Console.WriteLine(actual);
            Assert.AreEqual("(List<'a> -> (('a -> 'b) -> List<'b>))", actual);
        }

        [Test]
        public void OnlyAny()
        {
            Assert.AreEqual("Any", DS.type2str(DS.type_check(DS.TypeExpression.NewType_E(DS.Type.Any))));
        }

        [Test]
        public void OnlyAtom()
        {
            Assert.AreEqual("Atom", DS.type2str(DS.type_check(DS.TypeExpression.NewType_E(DS.Type.Atom))));
        }

        [Test]
        public void OnlyUnit()
        {
            Assert.AreEqual("IO", DS.type2str(DS.type_check(DS.TypeExpression.NewType_E(DS.Type.Unit))));
        }

        [Test]
        public void OnlyTrue()
        {
            Assert.AreEqual("True", DS.type2str(DS.type_check(DS.TypeExpression.NewType_E(DS.Type.True))));
        }

        [Test]
        public void OnlyFalse()
        {
            Assert.AreEqual("False", DS.type2str(DS.type_check(DS.TypeExpression.NewType_E(DS.Type.False))));
        }

        [Test]
        public void OnlyTypeId()
        {
            Assert.Throws(
                Is.TypeOf<Exception>().And.Message.EqualTo("Not allowed to use TypeId(x) in TypeExpression"),
                () => DS.type2str(DS.type_check(DS.TypeExpression.NewType_E(DS.Type.NewTypeId("x")))));
        }

        [Test]
        public void OnlyPolyType()
        {
            Assert.AreEqual("'a", DS.type2str(DS.type_check(DS.TypeExpression.NewType_E(DS.Type.NewPolyType("x")))));
        }

        [Test]
        public void OnlyList_Simple()
        {
            Assert.AreEqual("List<Atom>", DS.type2str(DS.type_check(DS.TypeExpression.NewType_E(DS.Type.NewList(DS.Type.Atom)))));
        }
    }
}
