using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.FSharp.Collections;
using NUnit.Framework;

using DynamicStatic;

namespace DynamicStaticTests
{
    [TestFixture]
    public class Tests
    {
        [Test]
        public void Identity()
        {
            var idType = DS.type_check(DS.id);
            Assert.AreEqual(DS.type2str(idType), "('a -> 'a)");

            var idCall1 = DS.TypeExpression.NewCall(
                DS.id, 
                DS.TypeExpression.NewType_E(DS.Type.Atom));

            Assert.AreEqual(DS.type2str(DS.type_check(idCall1)), "Atom");

            var idCall2 = DS.TypeExpression.NewCall(
                DS.id,
                DS.TypeExpression.NewType_E(DS.Type.Any));

            Assert.AreEqual(DS.type2str(DS.type_check(idCall2)), "Any");

            var idCall3 = DS.TypeExpression.NewCall(
                DS.id,
                DS.TypeExpression.NewType_E(
                    DS.Type.NewUnion(SetModule.OfSeq(
                        new List<DS.Type> { DS.Type.True, DS.Type.False }))));

            Assert.AreEqual(DS.type2str(DS.type_check(idCall3)), "{True|False}");
        }
    }
}
